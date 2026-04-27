;;;; CS 4820 — HW5 Grading Rubric
;;;; Load after student's file (in package :tp)

(in-package :tp)

;;; ---------- grading-only tolerant CNF normalization ----------

(defun grade-literalp (x)
  (or (symbolp x)
      (booleanp x)
      (and (consp x)
           (== (car x) 'not)
           (== (len x) 2))
      (and (consp x)
           (not (p-funp (car x))))))

(defun grade-normalize-clause (c)
  (cond
    ((and (consp c) (== (car c) 'or))
     c)

    ((and (consp c) (== (len c) 1))
     (list 'or (car c)))

    ((grade-literalp c)
     (list 'or c))

    (t
     (list 'or c))))

(defun grade-clause-list-p (x)
  (and (consp x)
       (not (== (car x) 'and))
       (every #'listp x)))

(defun grade-normalize-cnf (f)
  (cond
    ((== f t) t)
    ((== f nil) nil)

    ;; standard formula CNF: (and ...)
    ((and (consp f) (== (car f) 'and))
     (cons 'and (mapcar #'grade-normalize-clause (cdr f))))

    ;; list-of-clauses CNF: ((a b) ((not a) c) ...)
    ((grade-clause-list-p f)
     (cons 'and (mapcar #'grade-normalize-clause f)))

    ;; bare formula/literal as one-clause CNF
    (t
     (list 'and (grade-normalize-clause f)))))

(defun grade-clause->lits (c)
  (cond
    ((and (consp c) (== (car c) 'or))
     (cdr c))
    ((and (consp c) (== (len c) 1))
     c)
    (t
     (list c))))

(defun grade-clausep (x)
  (let ((c (grade-normalize-clause x)))
    (and (consp c)
         (== (car c) 'or)
         (every #'grade-literalp (cdr c)))))

(defun grade-cnfp (x)
  (let ((n (grade-normalize-cnf x)))
    (or (== n t)
        (== n nil)
        (and (consp n)
             (== (car n) 'and)
             (every #'grade-clausep (cdr n))))))

(defun grade-cnf->clauses (f)
  (let ((n (grade-normalize-cnf f)))
    (cond
      ((== n t) nil)
      ((== n nil) (list nil))
      (t (cdr n)))))

(defun grade-dp-aux (clauses)
  (dp (cons 'and (mapcar #'grade-normalize-clause clauses))))

(defun grade-dpll-aux (clauses)
  (if (fboundp 'dpll)
      (dpll (cons 'and (mapcar #'grade-normalize-clause clauses)))
    (grade-dp-aux clauses)))

;;; ---------- SAT verification ----------

(defun grade-eval-lit (lit asgn)
  (match lit
    ((type boolean) lit)
    ((list 'not inner)
     (let ((v (assoc inner asgn :test #'equal)))
       (if v (not (cdr v)) nil)))
    (_
     (let ((v (assoc lit asgn :test #'equal)))
       (if v (cdr v) nil)))))

(defun grade-eval-clause (clause asgn)
  (some #'(lambda (lit) (grade-eval-lit lit asgn))
        (grade-clause->lits (grade-normalize-clause clause))))

(defun grade-verify-sat (f asgn)
  (every #'(lambda (clause) (grade-eval-clause clause asgn))
         (grade-cnf->clauses f)))

;;; ---------- macros ----------

(defmacro check (label form)
  `(handler-case
       (progn ,form (format t "~&[PASS] ~a~%" ,label))
     (error (e)
       (format t "~&[FAIL] ~a — ~a~%" ,label e))))

(defmacro check-sat (label f)
  `(check ,label
     (multiple-value-bind (r a) (dp ,f)
       (assert (== r 'sat))
       (assert (grade-verify-sat ,f a)))))

(defmacro check-unsat (label f)
  `(check ,label
     (assert (== (car (multiple-value-list (dp ,f))) 'unsat))))

(defmacro check-dpll-sat (label f)
  `(check ,label
     (if (not (fboundp 'dpll))
         (error "dpll not defined")
       (multiple-value-bind (r a) (dpll ,f)
         (assert (== r 'sat))
         (assert (grade-verify-sat ,f a))))))

(defmacro check-dpll-unsat (label f)
  `(check ,label
     (if (not (fboundp 'dpll))
         (error "dpll not defined")
       (assert (== (car (multiple-value-list (dpll ,f))) 'unsat)))))

;;; Q1

(format t "~%=== Q1 p-simplify ===~%")

(check "A1" (assert-acl2s-equal (p-simplify '(and p t q)) '(and p q)))
(check "A2" (assert-acl2s-equal (p-simplify '(or p nil q)) '(or p q)))
(check "A3" (assert-acl2s-equal (p-simplify '(and)) t))
(check "A4" (assert-acl2s-equal (p-simplify '(and p)) 'p))
(check "A5" (assert-acl2s-equal (p-simplify '(and p t (foo t nil) q)) '(and p (foo t nil) q)))

(check "B1" (assert-acl2s-equal (p-simplify '(and p (and q r))) '(and p q r)))
(check "B2" (assert-acl2s-equal (p-simplify '(or p (or q r))) '(or p q r)))
(check "B3" (assert-acl2s-equal (p-simplify '(and p (and q (and r s)))) '(and p q r s)))

(check "C1" (assert-acl2s-equal (p-simplify '(and p nil q)) nil))
(check "C2" (assert-acl2s-equal (p-simplify '(or p t q)) t))

(check "D1" (assert-acl2s-equal (p-simplify '(not (not p))) 'p))
(check "D2" (assert-acl2s-equal (p-simplify '(not (iff p q))) '(xor p q)))
(check "D3" (assert-acl2s-equal (p-simplify '(not (xor p q))) '(iff p q)))
(check "D4" (assert-acl2s-equal (p-simplify '(not (iff p t))) '(not p)))

(check "E1" (assert-acl2s-equal (p-simplify '(and (or p q) (or r q p) p)) 'p))
(check "E2" (assert-acl2s-equal (p-simplify '(and p (implies p q))) '(and p q)))

(check "F1" (assert-acl2s-equal (p-simplify '(or x (not x))) t))
(check "F2" (assert-acl2s-equal (p-simplify '(and x (not x))) nil))
(check "F3" (assert-acl2s-equal (p-simplify '(or (foo a b) z (not (foo a b)))) t))

;;; Q2

(format t "~%=== Q2 tseitin ===~%")

(check "T1" (assert (grade-cnfp (tseitin '(and p q)))))
(check "T2" (assert (grade-cnfp (tseitin '(implies p q)))))
(check "T3" (assert (grade-cnfp (tseitin '(iff p q)))))
(check "T4" (assert (grade-cnfp (tseitin '(if p q r)))))


;; T5 (was: literal equality to t) — relaxed: equi-sat check
(check "T5"
  (let ((r (grade-normalize-cnf (tseitin '(or p (not p))))))
    ;; acceptable outputs: the boolean t, or a CNF that DP finds SAT
    (assert (or (== r t)
                (and (grade-cnfp r)
                     (== (car (multiple-value-list (dp r))) 'sat))))))


;; T6 (was: literal equality to '(and (or))) — relaxed: equi-sat check
(check "T6"
  (let ((r (grade-normalize-cnf (tseitin '(and p (not p))))))
    ;; acceptable outputs: the boolean nil, or a CNF that DP finds UNSAT
    (assert (or (== r nil)
                (and (grade-cnfp r)
                     (== (car (multiple-value-list (dp r))) 'unsat))))))



(check "T7"
  (let ((r (grade-normalize-cnf (tseitin '(and (foo x) (bar y))))))
    (assert (grade-cnfp r))))

#|
;; T8/T9: equi-satisfiability round-trips (normalize before passing to dp)
(check "T8"
  (multiple-value-bind (r _) (dp (grade-normalize-cnf (tseitin '(and (or p q) (implies r s)))))
    (assert (== r 'sat))))
|#


(check "T9"
  (multiple-value-bind (r _) (dp (grade-normalize-cnf (tseitin '(and p (not p)))))
    (assert (== r 'unsat))))

(check "T10"
  (let ((r (grade-normalize-cnf (tseitin '(or (foo a b) (bar c d))))))
    (assert (grade-cnfp r))))

;;; Q3

(format t "~%=== Q3 DP ===~%")

(check-sat   "D1 simple SAT"    '(and (or p q)))
(check-unsat "D2 simple UNSAT"  '(and (or p) (or (not p))))
(check-sat   "D3 BCP chain"     '(and (or p) (or (not p) q) (or (not q) r)))
(check-unsat "D4 empty clause"  '(and (or)))
(check-sat   "D5 pure literal"  '(and (or p q) (or p r)))

(check-unsat "D6 3-var UNSAT"
  '(and (or p q r) (or (not p) q r) (or p (not q) r)
        (or (not p) (not q) r) (or p q (not r))
        (or (not p) q (not r)) (or p (not q) (not r))
        (or (not p) (not q) (not r))))

(check-sat "D7 4-var SAT"
  '(and (or p q) (or (not p) r) (or (not r) s) (or (not s) q)))

(check "D8 assignment verifies"
  (multiple-value-bind (r a)
      (dp '(and (or p (not q)) (or (not p) r) (or q (not r))))
    (assert (== r 'sat))
    (assert (grade-verify-sat '(and (or p (not q)) (or (not p) r) (or q (not r))) a))))

(check-sat "D9 compound atoms"
  '(and (or (foo x) (bar y)) (or (not (foo x)) (baz z))))


;;; Q4

(format t "~%=== Q4 DPLL ===~%")

(check-dpll-sat   "L1 simple SAT"     '(and (or p q)))
(check-dpll-unsat "L2 empty clause"   '(and (or)))
(check-dpll-sat   "L3 BCP chain"      '(and (or p) (or (not p) q) (or (not q) r)))
(check-dpll-unsat "L4 BCP UNSAT"      '(and (or p) (or (not p))))

(check-dpll-unsat "L5 all-sign UNSAT"
  '(and (or a b) (or (not a) b) (or a (not b)) (or (not a) (not b))))

(check-dpll-sat "L6 L10 slide"
  '(and (or a b) (or b c) (or (not b) c d)
        (or (not a) (not x) y) (or (not a) x z)
        (or (not a) (not y) z) (or (not a) x (not z))
        (or (not a) (not y) (not z))))

(check "L7 assignment verifies"
  (if (not (fboundp 'dpll))
      (format t "~&[SKIP] dpll not defined~%")
    (multiple-value-bind (r a)
        (dpll '(and (or p (not q)) (or (not p) r) (or q (not r))))
      (assert (== r 'sat))
      (assert (grade-verify-sat '(and (or p (not q)) (or (not p) r) (or q (not r))) a)))))

(check-dpll-unsat "L8 3-var UNSAT"
  '(and (or p q r) (or (not p) q r) (or p (not q) r) (or (not p) (not q) r)
        (or p q (not r)) (or (not p) q (not r)) (or p (not q) (not r))
        (or (not p) (not q) (not r))))

(check-dpll-sat "L9 compound atoms"
  '(and (or (foo x) (bar y)) (or (not (foo x)) (baz z))))

(check "L10 tseitin round-trip"
  (if (not (fboundp 'dpll))
      (format t "~&[SKIP] dpll not defined~%")
    (multiple-value-bind (r _) (dpll (grade-normalize-cnf (tseitin '(and (or p q) (implies r s)))))
      (assert (== r 'sat)))))

;;; ============================================================
;;; BENCHMARK: DP Scientific Benchmark
;;; ============================================================

(defun ph-var (i j) `(pigeon ,i ,j))

(defun ph-at-least-one (i n)
  (mapcar (lambda (j) (ph-var i j))
          (loop for j from 1 to n collect j)))

(defun ph-no-conflict (n)
  (let ((clauses nil))
    (loop for j from 1 to n do
      (loop for i1 from 1 to (1+ n) do
        (loop for i2 from (1+ i1) to (1+ n) do
          (push (list `(not ,(ph-var i1 j))
                      `(not ,(ph-var i2 j)))
                clauses))))
    clauses))

(defun pigeonhole-cnf (n)
  (let ((clauses nil))
    (loop for i from 1 to (1+ n) do
      (push (ph-at-least-one i n) clauses))
    (append clauses (ph-no-conflict n))))


(format t "~%=== BENCHMARK: DP Scientific ===~%")

;;; --- Benchmark harness ---

(defparameter *bench-results* nil
  "Accumulated benchmark results: list of (name . ms)")

(defun bench-run (name thunk &optional (timeout 10))
  "Run THUNK, record wall-clock ms, push to *bench-results*.
   Returns (values result ms) or (values :timeout nil) if timeout exceeded."
  (handler-case
    (sb-ext:with-timeout timeout
      (let* ((start (get-internal-real-time))
             (result (funcall thunk))
             (ms (* 1000.0 (/ (- (get-internal-real-time) start)
                              internal-time-units-per-second))))
        (push (cons name ms) *bench-results*)
        (format t "  ~30a ~8,1f ms~%" name ms)
        (values result ms)))
    (sb-ext:timeout ()
      (format t "  ~30a ~8a~%" name "TIMEOUT")
      (push (cons name nil) *bench-results*)
      (values :timeout nil))))

(defun bench-report ()
  "Print a sorted summary of all benchmark results collected so far."
  (format t "~%--- DP Benchmark Summary (fastest to slowest) ---~%")
  (let* ((finished (remove-if #'(lambda (r) (null (cdr r))) *bench-results*))
         (sorted   (sort (copy-list finished) #'< :key #'cdr)))
    (dolist (r sorted)
      (format t "  ~30a ~8,1f ms~%" (car r) (cdr r)))
    (let ((timeouts (remove-if #'cdr *bench-results*)))
      (when timeouts
        (format t "~%  Timed out: ~{~a~^, ~}~%"
                (mapcar #'car timeouts))))))

;;; --- Problem families ---

;; 1. Pigeonhole (UNSAT) — already in rubric, but now timed via harness
;;    so results feed into the summary table

(format t "~%-- Pigeonhole (UNSAT) --~%")
(setf *bench-results* nil)

(dolist (n '(3 4 5 6))
  (let ((clauses (pigeonhole-cnf n)))
    (bench-run (format nil "pigeonhole-~a" n)
               #'(lambda () (grade-dp-aux clauses))
               15)))

;;; --- Final summary ---
(bench-report)


;;; BENCHMARK EC1

(format t "~%=== BENCHMARK EC1: DP ===~%")

(time
 (dp '(and (or p q r) (or (not p) q r) (or p (not q) r)
           (or (not p) (not q) r) (or p q (not r))
           (or (not p) q (not r)) (or p (not q) (not r))
           (or (not p) (not q) (not r)))))


;;; BENCHMARK EC2

(defun wire (prefix i)
  (intern (format nil "~a~a" prefix i)))

(defun make-rca (n)
  (cons 'and
        (loop for i below n
              for a   = (wire 'A i)
              for b   = (wire 'B i)
              for cin = (if (= i 0) nil (wire 'RC i))
              append
              `((iff ,(wire 'RS i) (xor ,a (xor ,b ,(or cin nil))))
                ,@(when (< i (1- n))
                    `((iff ,(wire 'RC (1+ i))
                           (or (and ,a ,b)
                               (and ,cin (xor ,a ,b))))))))))

(defun make-cla (n)
  (cons 'and
        (loop for i below n
              for a  = (wire 'A i)
              for b  = (wire 'B i)
              for cc = (if (= i 0) nil (wire 'CC i))
              append
              `((iff ,(wire 'CG i) (and ,a ,b))
                (iff ,(wire 'CP i) (xor ,a ,b))
                (iff ,(wire 'CS i) (xor ,(wire 'CP i) ,(or cc nil)))
                ,@(when (< i (1- n))
                    `((iff ,(wire 'CC (1+ i))
                           (or ,(wire 'CG i)
                               (and ,(wire 'CP i) ,cc)))))))))

(defun make-cec (n)
  `(and ,(make-rca n) ,(make-cla n)
        (or ,@(loop for i below n
                    collect `(xor ,(wire 'RS i) ,(wire 'CS i))))))

(format t "~%=== BENCHMARK EC2: DPLL — RCA vs CLA (all UNSAT) ===~%")

(if (not (fboundp 'dpll))
    (format t "~&[SKIP] dpll not defined — skipping EC2 benchmarks~%")
  (dolist (n '(4 8 12))
    (let ((cnf (grade-normalize-cnf (tseitin (make-cec n)))))
      (format t "~%-- ~a-bit --~%" n)
      (time (dpll cnf)))))

;;; Pigeonhole benchmark
#|
(defun ph-var (i j) `(pigeon ,i ,j))

(defun ph-at-least-one (i n)
  (mapcar (lambda (j) (ph-var i j))
          (loop for j from 1 to n collect j)))

(defun ph-no-conflict (n)
  (let ((clauses nil))
    (loop for j from 1 to n do
      (loop for i1 from 1 to (1+ n) do
        (loop for i2 from (1+ i1) to (1+ n) do
          (push (list `(not ,(ph-var i1 j))
                      `(not ,(ph-var i2 j)))
                clauses))))
    clauses))

(defun pigeonhole-cnf (n)
  (let ((clauses nil))
    (loop for i from 1 to (1+ n) do
      (push (ph-at-least-one i n) clauses))
    (append clauses (ph-no-conflict n))))
|#
(format t "~%=== BENCHMARK: Pigeonhole (always UNSAT) ===~%")

(format t "~%-- DP: 3 holes, 4 pigeons --~%")
(time (grade-dp-aux (pigeonhole-cnf 3)))

(format t "~%-- DP: 4 holes, 5 pigeons --~%")
(time (grade-dp-aux (pigeonhole-cnf 4)))

(format t "~%-- DP: 5 holes, 6 pigeons --~%")
(time (grade-dp-aux (pigeonhole-cnf 5)))

(if (not (fboundp 'dpll))
    (format t "~&[SKIP] dpll not defined — skipping DPLL pigeonhole benchmarks~%")
  (progn
    (format t "~%-- DPLL: 3 holes, 4 pigeons --~%")
    (time (grade-dpll-aux (pigeonhole-cnf 3)))

    (format t "~%-- DPLL: 4 holes, 5 pigeons --~%")
    (time (grade-dpll-aux (pigeonhole-cnf 4)))

    (format t "~%-- DPLL: 5 holes, 6 pigeons --~%")
    (time (grade-dpll-aux (pigeonhole-cnf 5)))))


