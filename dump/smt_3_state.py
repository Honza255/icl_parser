
from z3 import *

txt = "\
(declare-datatypes () ((x_bit ONE ZERO X))) \
\
(declare-const bit_0 x_bit)\
(declare-const bit_1 x_bit)\
(declare-const bit_2 x_bit)\
(declare-const bit_3 x_bit)\
\
(define-fun x_and ((s1 x_bit) (s2 x_bit)) x_bit\
  (match s1\
    (case X (match s2\
              (case X X)\
              (case ONE X)\
              (case ZERO ZERO)))\
    (case ONE (match s2\
                (case X X)\
                (case ONE ONE)\
                (case ZERO ZERO)))\
    (case ZERO (match s2\
                 (case X ZERO)\
                 (case ONE ZERO)\
                 (case ZERO ZERO)))))\
\
(define-fun x_or ((s1 x_bit) (s2 x_bit)) x_bit\
  (match s1\
    (case X (match s2\
              (case X X)\
              (case ONE ONE)\
              (case ZERO X)))\
    (case ONE (match s2\
                (case X ONE)\
                (case ONE ONE)\
                (case ZERO ONE)))\
    (case ZERO (match s2\
                 (case X X)\
                 (case ONE ONE)\
                 (case ZERO ZERO)))))\
\
(define-fun x_imp ((s1 x_bit) (s2 x_bit)) x_bit\
  (match s1\
    (case X (match s2\
              (case X X)\
              (case ONE ONE)\
              (case ZERO X)))\
    (case ONE (match s2\
                (case X X)\
                (case ONE ONE)\
                (case ZERO ZERO)))\
    (case ZERO (match s2\
                 (case X ONE)\
                 (case ONE ONE)\
                 (case ZERO ONE)))))\
\
(define-fun x_eq ((s1 x_bit) (s2 x_bit)) x_bit\
  (match s1\
    (case X (match s2\
              (case X ONE)\
              (case ONE ZERO)\
              (case ZERO ZERO)))\
    (case ONE (match s2\
                (case X ZERO)\
                (case ONE ONE)\
                (case ZERO ZERO)))\
    (case ZERO (match s2\
                 (case X ZERO)\
                 (case ONE ZERO)\
                 (case ZERO ONE)))))\
\
(define-fun x_eq_2 ((s1 x_bit) (s2 x_bit)) x_bit\
(ite (= s1 s2) ONE ZERO)) \
(assert (= ONE (x_or bit_0 bit_1)))\
(define-fun-rec length ((ls (List x_bit))) x_bit\
   ONE)\
"

cnf = parse_smt2_string(txt)


