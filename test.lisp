(in-package :tp)

;; Usage:
;; (load "chris5.lisp")
;; (load "goodgrader.lisp")
;; (load "test.lisp")
;; (in-package :tp)
;; (run-tests)

;;; ------------------------------------------------------------
;;; Result-only helpers
;;; ------------------------------------------------------------

(defun dp-result-only (f)
  (multiple-value-bind (r a) (dp f)
    (declare (ignore a))
    r))

(defun dpll-result-only (f)
  (multiple-value-bind (r a) (dpll f)
    (declare (ignore a))
    r))

;;; ------------------------------------------------------------
;;; Generic comparison helpers
;;; ------------------------------------------------------------

(defun compare-dp-dpll-on-cnf (cnf name)
  (format t "~%=== ~A ===~%" name)

  (multiple-value-bind (r1 a1) (dp cnf)
    (format t "  DP:   ~A~%" r1)
    (when (equal r1 'sat)
      (format t "  DP model valid? ~A~%" (verify-sat cnf a1))))

  (multiple-value-bind (r2 a2) (dpll cnf)
    (format t "  DPLL: ~A~%" r2)
    (when (equal r2 'sat)
      (format t "  DPLL model valid? ~A~%" (verify-sat cnf a2))))

  ;; Decision-procedure agreement check
  (let ((dp-res   (dp-result-only cnf))
        (dpll-res (dpll-result-only cnf)))
    (assert (equal dp-res dpll-res))
    dp-res))

(defun compare-dp-dpll-on-formula (f name)
  (compare-dp-dpll-on-cnf (tseitin f) name))

;;; ------------------------------------------------------------
;;; Adder tests
;;; ------------------------------------------------------------

(defun test-one-adder (n k)
  (let* ((f   (mk-adder-test n k))
         (cnf (tseitin f)))
    (format t "~%Testing adder n=~A k=~A~%" n k)
    (compare-dp-dpll-on-cnf cnf (format nil "adder n=~A k=~A" n k))))

(defun run-adder-tests ()
  (test-one-adder 2 1)
  (test-one-adder 2 2)
  (test-one-adder 3 1)
  (test-one-adder 3 2))

;;; ------------------------------------------------------------
;;; Basic CNF tests
;;; These test DP/DPLL directly, without Tseitin.
;;; ------------------------------------------------------------

(defun run-basic-cnf-tests ()
  (compare-dp-dpll-on-cnf
   '(and (or p q))
   "basic sat")

  (compare-dp-dpll-on-cnf
   '(and (or p) (or (not p)))
   "basic unsat")

  (compare-dp-dpll-on-cnf
   '(and (or p q) (or (not p) r))
   "small sat")

  (compare-dp-dpll-on-cnf
   '(and (or a b)
         (or (not a) b)
         (or a (not b))
         (or (not a) (not b)))
   "xor-style unsat")

  (compare-dp-dpll-on-cnf
   '(and (or (foo x) (bar y))
         (or (not (foo x)) (baz z)))
   "compound atoms sat"))

;;; ------------------------------------------------------------
;;; Formula tests through Tseitin
;;; These test simplification + Tseitin + solver decisions.
;;; ------------------------------------------------------------

(defun run-formula-tests ()
  (compare-dp-dpll-on-formula
   '(implies p p)
   "formula implies p p")

  (compare-dp-dpll-on-formula
   '(implies p q)
   "formula implies p q")

  (compare-dp-dpll-on-formula
   '(implies (and p q) p)
   "formula implies (and p q) p")

  (compare-dp-dpll-on-formula
   '(iff p q)
   "formula iff")

  (compare-dp-dpll-on-formula
   '(xor p q)
   "formula xor")

  (compare-dp-dpll-on-formula
   '(and (or p (iff q r))
         (implies s (xor p q)))
   "formula nested"))

;;; ------------------------------------------------------------
;;; Tiny sanity checks for constants
;;; ------------------------------------------------------------

(defun run-constant-tests ()
  (format t "~%=== constant tests ===~%")
  (format t "  DP t: ~A~%" (dp-result-only t))
  (format t "  DP nil: ~A~%" (dp-result-only nil))
  (format t "  DPLL t: ~A~%" (dpll-result-only t))
  (format t "  DPLL nil: ~A~%" (dpll-result-only nil))

  (assert (equal (dp-result-only t) 'sat))
  (assert (equal (dp-result-only nil) 'unsat))
  (assert (equal (dpll-result-only t) 'sat))
  (assert (equal (dpll-result-only nil) 'unsat)))

;;; ------------------------------------------------------------
;;; Optional: CNF stats
;;; ------------------------------------------------------------

(defun cnf-stats (cnf)
  (let ((clauses (cnf->clauses cnf)))
    (list :num-clauses (length clauses)
          :num-atoms   (length (clauses->atoms clauses))
          :avg-clause-len
          (/ (reduce #'+ (mapcar (lambda (c) (length (clause->lits c))) clauses))
             (max 1 (length clauses))))))

(defun show-adder-stats (n k)
  (let* ((f   (mk-adder-test n k))
         (cnf (tseitin f)))
    (format t "~%Adder stats n=~A k=~A: ~S~%" n k (cnf-stats cnf))))

;;; ------------------------------------------------------------
;;; Optional: benchmarking
;;; ------------------------------------------------------------

(defun benchmark-one-adder (n k)
  (let* ((f   (mk-adder-test n k))
         (cnf (tseitin f)))
    (format t "~%=== benchmark adder n=~A k=~A ===~%" n k)
    (format t "CNF stats: ~S~%" (cnf-stats cnf))

    (format t "~%DP...~%")
    (time
     (multiple-value-bind (r a) (dp cnf)
       (declare (ignore a))
       (format t "  result: ~A~%" r)))

    (format t "~%DPLL...~%")
    (time
     (multiple-value-bind (r a) (dpll cnf)
       (declare (ignore a))
       (format t "  result: ~A~%" r)))))

;;; ------------------------------------------------------------
;;; Main entry points
;;; ------------------------------------------------------------

(defun run-tests ()
  (run-constant-tests)
  (run-basic-cnf-tests)
  (run-formula-tests)
  (run-adder-tests)
  (format t "~%All decision tests passed.~%"))

(defun run-benchmarks ()
  (benchmark-one-adder 2 1)
  (benchmark-one-adder 2 2)
  (benchmark-one-adder 3 1)
  (benchmark-one-adder 3 2))