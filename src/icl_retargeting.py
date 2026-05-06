import re
import os
from typing import NamedTuple

from z3 import *

from .icl_common import *
from .icl_items import *

current_dir = os.path.dirname(os.path.abspath(__file__))


# ── S-expression pretty-printer ───────────────────────────────────────────────

def _sexpr_split(body: str) -> list[str]:
    """Split the interior of an S-expression into its top-level children."""
    tokens: list[str] = []
    depth  = 0
    start  = 0
    body   = body.strip()
    for i, ch in enumerate(body):
        if ch == '(':
            if depth == 0:
                start = i
            depth += 1
        elif ch == ')':
            depth -= 1
            if depth == 0:
                tokens.append(body[start : i + 1])
                start = i + 1
        elif ch == ' ' and depth == 0:
            tok = body[start:i].strip()
            if tok:
                tokens.append(tok)
            start = i + 1
    last = body[start:].strip()
    if last:
        tokens.append(last)
    return tokens


def _pp_sexpr(s: str, col: int = 0, max_col: int = 100) -> str:
    """Recursively pretty-print an S-expression, breaking lines when too wide.

    col     — current column offset (used to decide whether to break)
    max_col — target line-width threshold
    """
    if col + len(s) <= max_col or '(' not in s:
        return s
    if not s.startswith('('):
        return s
    children = _sexpr_split(s[1:-1])
    if len(children) <= 1:
        return s
    head      = children[0]
    args      = children[1:]
    child_col = col + 2
    formatted = [_pp_sexpr(a, child_col, max_col) for a in args]
    sep       = "\n" + " " * child_col
    return f"({head}{sep}{sep.join(formatted)})"


class ScanBvInfo(NamedTuple):
    """Describes how a single scan-register bit maps into a Z3 BitVec word."""
    reg_name:  str   # register hierarchy name (dots → underscores)
    width:     int   # total register bit-width
    bit_index: int   # this bit's position within the word


class SolverPair(NamedTuple):
    """Holds the satisfiability solver and optimizer built for a given JTAG step count."""
    solver:    Solver
    optimizer: Optimize


class LVec:
    """Logic Vector: dual-BitVec three-valued logic (0 / 1 / X).

    values[j]=v, defined[j]=1  →  bit j is known and equals v
    values[j]=0, defined[j]=0  →  bit j is X (unknown)

    Canonical invariant enforced by constraint: (values & ~defined) == 0
    (X positions must carry value 0 so the encoding is unique).
    """
    __slots__ = ("values", "defined")

    def __init__(self, values, defined):
        self.values  = values   # Z3 BitVec: concrete bit values (0 where X)
        self.defined = defined  # Z3 BitVec: 1 = known, 0 = X

    @staticmethod
    def from_name(name: str, width: int) -> "LVec":
        return LVec(BitVec(f"val_{name}", width), BitVec(f"def_{name}", width))

    @property
    def size(self) -> int:
        return self.values.size()

    @property
    def canonical(self):
        return (self.values & ~self.defined) == BitVecVal(0, self.size)

    def changes(self, other: "LVec"):
        """Count bits that differ between self and other where both are defined.

        Returns Z3 Int: popcount(self.defined & other.defined & (self.values ^ other.values))
        """
        changed_and_known = self.defined & other.defined & (self.values ^ other.values)
        return Sum([
            If(Extract(j, j, changed_and_known) == BitVecVal(1, 1), IntVal(1), IntVal(0))
            for j in range(self.size)
        ])


def _format_smt2_debug(solver: Solver, num_steps: int) -> str:
    """Format solver constraints as human-readable SMT2 for debugging.

    Improvements over solver.to_smt2():
      - ``(declare-fun X () T)``  →  ``(declare-const X T)``
      - declarations grouped by step with section comments
      - declarations sorted by type within each step:
        val_scan → def_scan → sel_ → IS_IT_IR → soft_reg → sel_group → soft_all → other
      - assertions rendered flat via ``.sexpr()`` (no let-chain aliasing)
      - long assertions indented with _pp_sexpr
    """
    raw = solver.to_smt2()

    # ── parse declarations ────────────────────────────────────────────────
    decl_re = re.compile(
        r'\(declare-fun\s+(\S+)\s+\(\)\s+(.*?)\s*\)\s*$', re.MULTILINE
    )
    declarations: dict[str, str] = {}
    for m in decl_re.finditer(raw):
        name = m.group(1)
        typ  = m.group(2).strip()
        declarations[name] = f"(declare-const {name} {typ})"

    # ── group by trailing step number ─────────────────────────────────────
    step_suffix_re = re.compile(r'_(\d+)$')

    def _priority(name: str) -> int:
        if name.startswith('val_scan_'):                         return 0
        if name.startswith('def_scan_'):                         return 1
        if name.startswith('sel_') and 'group' not in name:     return 2
        if name.startswith('IS_IT_IR_DATA_CHAIN'):               return 3
        if name.startswith('soft_reg_'):                         return 4
        if name.startswith('sel_group_'):                        return 5
        if name == 'soft_all':                                   return 6
        return 7

    step_decls:   dict[int, list[str]] = {}
    global_decls: list[str]            = []
    for name in declarations:
        m = step_suffix_re.search(name)
        if m:
            step_decls.setdefault(int(m.group(1)), []).append(name)
        else:
            global_decls.append(name)

    # ── build output ──────────────────────────────────────────────────────
    bar = '─' * 48
    out: list[str] = [f"; SMT2 debug dump — {num_steps + 1} JTAG step(s)", ""]

    for step_num in sorted(step_decls):
        label = (
            "step 0 — initial state" if step_num == 0 else
            f"step {step_num} — after JTAG vector {step_num}"
        )
        out += [f"; ── {label} {bar}", ""]
        for n in sorted(step_decls[step_num], key=lambda n: (_priority(n), n)):
            out.append(declarations[n])
        out.append("")

    if global_decls:
        out += [f"; ── global {bar}", ""]
        for n in sorted(global_decls, key=lambda n: (_priority(n), n)):
            out.append(declarations[n])
        out.append("")

    # ── flat assertions (no let-chain aliasing) ───────────────────────────
    out += [f"; ── assertions {bar}", ""]
    for assertion in solver.assertions():
        flat   = assertion.sexpr()
        pretty = _pp_sexpr(flat, col=0, max_col=92)
        if '\n' in pretty:
            pretty = pretty.replace('\n', '\n        ')
        out.append(f"(assert {pretty})")
    out += ["", "(check-sat)", ""]

    return "\n".join(out)


class IclRetargeting:

    C_IR_DR_STATE = "IS_IT_IR_DATA_CHAIN"

    # ── tiny helpers ──────────────────────────────────────────────────────────

    @staticmethod
    def _step_smt2(expr: str, step: int) -> str:
        """Stamp _{step} onto every _NNNN token in a raw SMT2 expression string."""
        return re.sub(r'([\w.]+)(_\d+)', rf'\1\2_{step}', expr)

    @staticmethod
    def _constrain(solver: Solver, optimizer: Optimize, constraints) -> None:
        """Add constraints to both the satisfiability solver and the optimizer."""
        solver.add(constraints)
        optimizer.add(constraints)

    # ── scan-register BitVec mapping ─────────────────────────────────────────

    def _populate_scan_bit_to_bv(self) -> None:
        """Pre-compute bit-name → ScanBvInfo for every scan register.

        Must be called before any SMT2 or Z3 variable generation.
        """
        for _, scan_reg in self.scan_registers.items():
            scan_reg: IclScanRegister = scan_reg
            bit_names = scan_reg.get_all_named_indexes()
            reg_width = len(bit_names)
            reg_name  = scan_reg.get_name_with_hier()
            for bit_index, raw_bit_name in enumerate(bit_names):
                bit_name_clean = raw_bit_name
                self._scan_bit_to_bv[bit_name_clean] = ScanBvInfo(reg_name, reg_width, bit_index)

    def _replace_scan_bits_in_smt2(self, smt2_expr: str) -> str:
        """Replace Bool scan-bit references with BitVec extraction expressions.

        Example: "SIB_10_SR_0000_1" → "(= ((_ extract 0 0) val_scan_SIB_10_SR_1) #b1)"
        """
        def _replace_one(match):
            bit_name = match.group(1)   # e.g. "SIB_10_SR_0000"
            step_str = match.group(2)   # e.g. "1"
            if bit_name not in self._scan_bit_to_bv:
                return match.group(0)
            info            = self._scan_bit_to_bv[bit_name]
            bitvec_var_name = f"val_scan_{info.reg_name}_{step_str}"
            return f"(= ((_ extract {info.bit_index} {info.bit_index}) {bitvec_var_name}) #b1)"

        return re.sub(r'\b([A-Za-z_.]\w*_\d{4})_(\d+)\b', _replace_one, smt2_expr)

    # ── SMT2-string parsing helpers ──────────────────────────────────────────

    def _parse_dr_smt2(self, declarations_smt2: str, assertions_smt2: str) -> list:
        """Parse data-register SMT2 (string-based) into Z3 constraints.

        - Replaces scan-bit Bool references with BitVec extractions.
        - Pre-declares all val_scan_ BitVec variables for every step.
        - Declares any remaining undeclared Bool variable references.
        """
        full_smt2 = (declarations_smt2 + assertions_smt2)
        full_smt2 = self._replace_scan_bits_in_smt2(full_smt2)

        # Pre-declare val_scan_ BitVec for all steps (0 … max+1)
        all_steps   = range(self.max_allowed_steps + 2)
        reg_widths  = {info.reg_name: info.width for info in self._scan_bit_to_bv.values()}
        bitvec_declarations = "".join(
            f"(declare-const val_scan_{reg_name}_{s} (_ BitVec {width}))\n"
            for reg_name, width in reg_widths.items()
            for s in all_steps
        )

        already_declared = set(re.findall(r'\(declare-const\s+(\S+)', full_smt2))
        already_declared |= {f"val_scan_{r}_{s}" for r in reg_widths for s in all_steps}

        # Declare remaining undeclared Bool references
        missing_bool_declarations = ""
        known_names = set(already_declared)
        for match in re.finditer(r'\b([A-Za-z_][A-Za-z0-9_.]*_\d+)\b', full_smt2):
            name = match.group(1)
            if name not in known_names:
                missing_bool_declarations += f"(declare-const {name} Bool)\n"
                known_names.add(name)

        complete_smt2 = bitvec_declarations + missing_bool_declarations + full_smt2
        return list(z3.parse_smt2_string(complete_smt2))

    def _build_mini_constraint_z3(
        self, bool_var_name: str, rhs_template: str, step: int
    ) -> list:
        """Parse a single Bool equality (bool_var_name == rhs) into Z3 via mini SMT2.

        bool_var_name  — already step-suffixed and dots→underscores
        rhs_template   — raw (un-stepped) SMT2 expression; step is stamped here
        step           — JTAG step number
        Returns list of Z3 assertions.
        """
        rhs_stepped = self._step_smt2(rhs_template, step)
        rhs_stepped = self._replace_scan_bits_in_smt2(rhs_stepped)

        # Declare val_scan_ BitVec variables for this step
        declared_bitvecs    = set()
        bitvec_declarations = ""
        for info in self._scan_bit_to_bv.values():
            bitvec_var_name = f"val_scan_{info.reg_name}_{step}"
            if bitvec_var_name not in declared_bitvecs:
                bitvec_declarations += (
                    f"(declare-const {bitvec_var_name} (_ BitVec {info.width}))\n"
                )
                declared_bitvecs.add(bitvec_var_name)

        # Declare Bool variable references appearing in the RHS
        bool_declarations = ""
        declared_bools    = {bool_var_name}
        for match in re.finditer(r'\b([A-Za-z_][A-Za-z0-9_.]*_\d+)\b', rhs_stepped):
            name = match.group(1)
            if name not in declared_bools and not name.startswith('val_scan_'):
                bool_declarations += f"(declare-const {name} Bool)\n"
                declared_bools.add(name)

        mini_smt2 = (
            bitvec_declarations
            + bool_declarations
            + f"(declare-const {bool_var_name} Bool)\n"
            + f"(assert (= {bool_var_name} {rhs_stepped}))\n"
        )
        return list(z3.parse_smt2_string(mini_smt2))

    # ── constraint builders ──────────────────────────────────────────────────

    def _add_one_hot_and_ir_chain(
        self, solver: Solver, optimizer: Optimize, step: int
    ) -> None:
        
        # Ono-hot for interfaces - only one interface can be active in one step
        interfaces = []
        assert(len(self.one_hot_scan_interfaces) > 0)
        for name, scan_out_ports in self.one_hot_scan_interfaces.items():
            interface = Bool(self._step_smt2(f"{name}_0000", step))
            interfaces.append(interface)
            active_scan_out_ports = [
                Bool(self._step_smt2(v, step))
                for v in scan_out_ports
            ]
            interface_const = interface == And(*active_scan_out_ports)
            self._constrain(solver, optimizer, interface_const)
        one_hot_constraint = ( Sum(interfaces) == 1)
        self._constrain(solver, optimizer, one_hot_constraint)

        """Add one-hot control and IS_IT_IR_DATA_CHAIN constraints for the given step."""
        # for group in self.one_hot_groups:
        #    sel_bits = [
        #        Bool(self._step_smt2(v, step))
        #        for v in group.one_hot_bits
        #    ]
        #    if sel_bits:
        #        one_hot_constraint = (
        #            Sum([If(b, IntVal(1), IntVal(0)) for b in sel_bits]) == IntVal(1)
        #        )
        #        self._constrain(solver, optimizer, one_hot_constraint)

        ir_chain_active = Bool(f"{self.C_IR_DR_STATE}_{step}")
        ir_output_bits  = [
            Bool(self._step_smt2(v, step))
            for v in self.ir_out_ports
        ]
        if ir_output_bits:
            self._constrain(solver, optimizer, [
                Implies(ir_chain_active, And(*ir_output_bits)),
                Implies(Not(ir_chain_active), Not(Or(*ir_output_bits))),
            ])
        else:
            self._constrain(solver, optimizer, Not(ir_chain_active))

    def define_scan_registers_pure_bv(
        self,
        from_step: int,
        to_step: int,
        include_constraints: bool,
    ) -> tuple:
        """Build Z3 constraints for all scan registers between two JTAG steps.

        Returns (constraints: list[BoolRef], soft_cost_terms: list[ArithRef]).
        Each register gets val_scan_ + def_scan_ BitVec(N) at each step.
        """
        constraints     = []
        soft_cost_terms = []

        for _, scan_reg in self.scan_registers.items():
            scan_reg: IclScanRegister = scan_reg
            reg_name  = scan_reg.get_name_with_hier()
            reg_width = len(scan_reg.get_all_named_indexes())

            # Selection signal — RHS may reference BitVec extractions, so mini-SMT2 parse
            sel_var_name = f"sel_{reg_name}_0000_{to_step}"
            constraints.extend(self._build_mini_constraint_z3(
                sel_var_name, scan_reg.scan_selection_smt, to_step
            ))

            # Canonical 3VL invariant: value bits must be 0 wherever undefined (X)
            val_new = BitVec(f"val_scan_{reg_name}_{to_step}", reg_width)
            def_new = BitVec(f"def_scan_{reg_name}_{to_step}", reg_width)
            constraints.append((val_new & ~def_new) == BitVecVal(0, reg_width))

            if include_constraints:
                val_old      = BitVec(f"val_scan_{reg_name}_{from_step}", reg_width)
                def_old      = BitVec(f"def_scan_{reg_name}_{from_step}", reg_width)
                was_selected = Bool(f"sel_{reg_name}_0000_{from_step}")

                # Not selected → register contents frozen across this step
                constraints.append(
                    Implies(Not(was_selected), And(val_old == val_new, def_old == def_new))
                )

                # Selected → all bits become known (TDI values are always concrete)
                all_ones = BitVecVal((1 << reg_width) - 1, reg_width)
                constraints.append(Implies(was_selected, def_new == all_ones))

                # Soft cost: deviation from the reference state.
                # Known bits → reference is the old value (minimise disturbance).
                # X bits     → reference is the register default value.

                default_int = scan_reg.default_value.copy()
                default_int.bit_reversal()
                default_int = default_int.get_number()

                default_bv     = BitVecVal(default_int, reg_width)
                merged_ref_val = (val_old & def_old) | (default_bv & ~def_old)
                merged_ref     = LVec(merged_ref_val, all_ones)  # every bit has a preference
                state_after    = LVec(val_new, def_new)
                bit_change_cost = Real(f"soft_reg_{reg_name}_{to_step}")
                constraints.append(bit_change_cost == ToReal(merged_ref.changes(state_after)))
                soft_cost_terms.append(bit_change_cost)

        return constraints, soft_cost_terms

    # ── construction ─────────────────────────────────────────────────────────

    def __init__(
        self,
        scan_registers:   dict[str, IclScanRegister],
        data_registers:   dict[str, smtDataReg],
        sel_muxes:        dict[str, str],
        one_hot_groups:   list[smtOneHotGroup],
        ir_out_ports:     list[str],
        max_allowed_steps: int,
        one_hot_scan_interfaces: dict[str,list[str]]        
    ) -> None:

        self.scan_registers    = scan_registers
        self.data_registers    = data_registers
        self.sel_muxes         = sel_muxes
        self.max_allowed_steps = max_allowed_steps
        self.one_hot_groups:  list[smtOneHotGroup] = one_hot_groups
        self.ir_out_ports:    list[str]             = ir_out_ports
        self.one_hot_scan_interfaces: dict[str,list[str]] = one_hot_scan_interfaces
        
        self.end_step  = None
        self.end_model = None

        # Maps clean bit name (dots→underscores, no step suffix) → ScanBvInfo
        self._scan_bit_to_bv: dict[str, ScanBvInfo] = {}
        self._populate_scan_bit_to_bv()

        self.retarget_solvers: dict[int, SolverPair] = {}
        self.created_solvers: dict[int, SolverPair] = {}
        
        self.set_max_steps(max_allowed_steps)
        
    def set_max_steps(self, max_steps: int):
        assert(max_steps > 1)

        self.retarget_solvers = {}       
        self.max_allowed_steps = max_steps

        for solver_step in range(self.max_allowed_steps):

            if(solver_step in self.created_solvers):
                self.retarget_solvers[solver_step] = self.created_solvers[solver_step]
                continue

            soft_cost_terms: list = []
            solver    = Solver()
            optimizer = Optimize()

            # ── step 0: declare initial-state variables ───────────────────────
            init_constraints, _ = self.define_scan_registers_pure_bv(0, 0, False)
            self._constrain(solver, optimizer, init_constraints)

            for mux_name, mux_expr in self.sel_muxes.items():
                mux_var_name    = f"{mux_name}_0"
                mux_constraints = self._build_mini_constraint_z3(mux_var_name, mux_expr, 0)
                self._constrain(solver, optimizer, mux_constraints)

            self._add_one_hot_and_ir_chain(solver, optimizer, 0)

            # ── transition steps 0→1, 1→2, … ─────────────────────────────────
            transition_steps = list(range(solver_step + 1))
            for from_step in transition_steps:
                to_step = from_step + 1

                scan_constraints, scan_soft_costs = self.define_scan_registers_pure_bv(
                    from_step, to_step, True
                )
                self._constrain(solver, optimizer, scan_constraints)
                soft_cost_terms.extend(scan_soft_costs)

                for mux_name, mux_expr in self.sel_muxes.items():
                    mux_var_name    = f"{mux_name}_{to_step}"
                    mux_constraints = self._build_mini_constraint_z3(mux_var_name, mux_expr, to_step)
                    self._constrain(solver, optimizer, mux_constraints)

                self._add_one_hot_and_ir_chain(solver, optimizer, to_step)

            # ── sel_group: was each scan reg selected in any step? ────────────
            for _, scan_reg in self.scan_registers.items():
                reg_name = scan_reg.get_name_with_hier()
                ever_selected     = Bool(f"sel_group_{reg_name}")
                per_step_sel_vars = [Bool(f"sel_{reg_name}_0000_{s}") for s in transition_steps]
                self._constrain(solver, optimizer, ever_selected == Or(*per_step_sel_vars))

            # ── sel_group: was each data reg written in any step? ─────────────
            for _, data_reg in self.data_registers.items():
                reg_name      = data_reg.full_name
                ever_written  = Bool(f"sel_group_data_reg_written_{reg_name}")
                per_step_wr_vars = [
                    Bool(f"write_enabled_{reg_name}_0000_{s + 1}") for s in transition_steps
                ]
                self._constrain(solver, optimizer, ever_written == Or(*per_step_wr_vars))

            # ── soft_all: total bit-change cost ───────────────────────────────
            cost_terms = [
                Real(st) if isinstance(st, str) else st
                for st in soft_cost_terms
            ]
            total_bit_change_cost = Real("soft_all")
            cost_sum = sum(cost_terms[1:], cost_terms[0]) if cost_terms else RealVal(0)
            self._constrain(solver, optimizer, total_bit_change_cost == cost_sum)

            ## ── debug dump ────────────────────────────────────────────────────
            #with open(f"{current_dir}/tmp/latest_{num_allowed_steps}_smt2.txt", "w") as f:
            #    f.write(_format_smt2_debug(solver, num_allowed_steps))

            self.retarget_solvers[solver_step] = SolverPair(solver, optimizer)
            self.created_solvers[solver_step] = self.retarget_solvers[solver_step]

    # ── state encoding ────────────────────────────────────────────────────────

    def _bv_state_z3(
        self, bit_states: dict, step: int, pin_x_as_unknown: bool = False
    ) -> tuple:
        """Convert a bit-state dict into Z3 constraints.

        bit_states keys are plain bit names (no step suffix), e.g. "SR_0_0000_0".
        Scan-register bits become BitVec constraints; everything else goes into
        bool_bit_states for Bool handling.

        pin_x_as_unknown — set True for the **initial** state.  For every scan
            register that appears in bit_states, X-valued bit positions get an
            explicit ``(def & x_mask) == 0`` constraint.  This prevents the
            optimizer from setting def=1 for unknown positions to make the
            merged-reference match the target for free (cost 0 exploit).
            For the **target** state leave False: X target bits are simply absent
            from the dict, so no constraint is needed.

        Returns (bv_constraints: list, bool_bit_states: dict).
        """
        per_reg_state:   dict = {}
        bool_bit_states: dict = {}

        for bit_name, bit_value in bit_states.items():
            if bit_name in self._scan_bit_to_bv:
                info    = self._scan_bit_to_bv[bit_name]
                reg_key = (info.reg_name, info.width)
                # When pinning X bits we need an entry for every register seen,
                # even if all its bits are X.
                if pin_x_as_unknown and reg_key not in per_reg_state:
                    per_reg_state[reg_key] = {
                        "width": info.width, "value_word": 0, "defined_mask": 0
                    }
                if bit_value[0] not in ("x", "X"):
                    if reg_key not in per_reg_state:
                        per_reg_state[reg_key] = {
                            "width": info.width, "value_word": 0, "defined_mask": 0
                        }
                    per_reg_state[reg_key]["value_word"]  |= int(bit_value[0]) << info.bit_index
                    per_reg_state[reg_key]["defined_mask"] |= 1 << info.bit_index
            else:
                bool_bit_states[bit_name] = bit_value

        constraints = []
        for (reg_name, width), state in per_reg_state.items():
            val_bitvec   = BitVec(f"val_scan_{reg_name}_{step}", width)
            def_bitvec   = BitVec(f"def_scan_{reg_name}_{step}", width)
            defined_mask = state["defined_mask"]
            value_word   = state["value_word"]

            if defined_mask == (1 << width) - 1:
                # All bits known: pin the entire word
                constraints.append(val_bitvec == BitVecVal(value_word, width))
                constraints.append(def_bitvec == BitVecVal(defined_mask, width))
            else:
                mask_bv = BitVecVal(defined_mask, width)
                if defined_mask > 0:
                    # Pin the known bit positions
                    constraints.append((val_bitvec & mask_bv) == BitVecVal(value_word, width))
                    constraints.append((def_bitvec & mask_bv) == mask_bv)
                if pin_x_as_unknown:
                    # Force def=0 for X positions so the optimizer cannot treat
                    # unknown bits as already-known (which would collapse the cost).
                    x_mask_int = ((1 << width) - 1) & ~defined_mask
                    constraints.append(
                        (def_bitvec & BitVecVal(x_mask_int, width)) == BitVecVal(0, width)
                    )
                # Canonical 3VL invariant: value must be 0 wherever undefined
                constraints.append((val_bitvec & ~def_bitvec) == BitVecVal(0, width))

        return constraints, bool_bit_states

    def _bool_state_z3(self, bool_bit_states: dict, step: int) -> list:
        """Build Z3 Bool constraints for non-scan-reg state entries.

        Keys are plain names (no step suffix); _{step} is appended here.
        X-valued bits are left unconstrained.
        """
        constraints = []
        for bit_name, bit_value in bool_bit_states.items():
            if bit_value[0] in ("x", "X"):
                continue
            bool_var = Bool(f"{bit_name}_{step}")
            constraints.append(bool_var if bit_value[0] == "1" else Not(bool_var))
        return constraints

    # ── solving ───────────────────────────────────────────────────────────────

    def retarget(
        self,
        initial_scan_state: dict,
        target_scan_state:  dict,
        other_constraints:  dict,
    ) -> int:
        init_bv, init_bool_remaining = self._bv_state_z3(
            initial_scan_state, 0, pin_x_as_unknown=True
        )
        initial_constraints = init_bv + self._bool_state_z3(init_bool_remaining, 0)

        extra_constraints = []
        if other_constraints:
            for name, value in other_constraints.items():
                bool_var = Bool(name)
                extra_constraints.append(bool_var if value == 1 else Not(bool_var))

        for num_transitions, pair in self.retarget_solvers.items():
            print(f"solve step {num_transitions}")

            target_constraints = []
            if target_scan_state:
                tgt_bv, tgt_bool_remaining = self._bv_state_z3(
                    target_scan_state, num_transitions + 1
                )
                target_constraints = tgt_bv + self._bool_state_z3(
                    tgt_bool_remaining, num_transitions + 1
                )

            per_call_constraints = initial_constraints + extra_constraints + target_constraints

            pair.solver.push()
            pair.solver.add(per_call_constraints)
            if pair.solver.check() != sat:
                pair.solver.pop()
                continue
            self.end_step = num_transitions + 1
            pair.solver.pop()

            pair.optimizer.push()
            pair.optimizer.add(per_call_constraints)
            total_cost = Real("soft_all")
            pair.optimizer.minimize(total_cost)
            if pair.optimizer.check() != sat:
                pair.optimizer.pop()
                raise RuntimeError("Optimizer failed")
            self.end_step  = num_transitions + 1
            self.end_model = pair.optimizer.model()
            print("Bit changes", self.end_model.evaluate(total_cost))
            pair.optimizer.pop()
            return 0

        print(
            f"Retargeting failed: cannot reach target state within "
            f"{self.max_allowed_steps} JTAG vectors."
        )
        return 1

    # ── model query ───────────────────────────────────────────────────────────

    def print_model_states(self, model, prefix: str = "") -> None:
        for var in model:
            print(prefix, " Var: ", var, "Value:", model[var])

    def get_steps(self) -> list[int]:
        return list(range(0, self.end_step + 1))

    def get_bit(self, name: str, step: int) -> bool:
        bit_name = name

        # Scan-register bits are packed into BitVec words — extract from val_scan_
        if bit_name in self._scan_bit_to_bv:
            info           = self._scan_bit_to_bv[bit_name]
            val_bitvec     = BitVec(f"val_scan_{info.reg_name}_{step}", info.width)
            register_value = self.end_model.eval(val_bitvec, model_completion=True).as_long()
            return bool((register_value >> info.bit_index) & 1)

        # All other variables are plain Bool
        bool_var_name = f"{bit_name}_{step}"
        bool_var      = Bool(bool_var_name)
        bool_result   = self.end_model.eval(bool_var, model_completion=True)
        return is_true(bool_result)

    '''
    def get_data(self) -> dict[int, dict[str, bool]]:
        model_data: dict[int, dict[str, bool]] = {}
        for z3_var in self.end_model:
            var_name   = str(z3_var)
            step_match = re.search(r'_(\d+)$', var_name)
            if step_match:
                step_num      = int(step_match.group(1))
                var_base_name = var_name[:step_match.start()]
                model_data.setdefault(step_num, {})[var_base_name] = (
                    is_true(self.end_model[z3_var])
                )
        return model_data
    '''