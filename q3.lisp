#|

 Copyright © 2026 by Pete Manolios 
 CS 4820 Fall 2026

 Homework 4.
 Due: 2/16 (Midnight)

 For this assignment, work in groups of 1-2. Send me and the grader
 exactly one solution per team and make sure to follow the submission
 instructions on the course Web page. In particular, make sure that
 the subject of your email submission is "CS 4820 HWK 4".

 The group members are:
 Christopher Wright-Williams

|#





(in-package "ACL2S")
(set-gag-mode nil)
(modeling-admit-all)

; Q3a. We are using the definition on page 129.

;; for if-expr, conditional can appear in condition position
;; for normative, conditional cannot appear in condition position
(defdata if-atom (or bool var))
(defdata if-expr (or if-atom (list 'if if-expr if-expr if-expr)))
(defdata norm-if-expr (or if-atom (list 'if if-atom norm-if-expr norm-if-expr)))

; Notice that norm-if-expr is a subtype of if-expr.
(defdata-subtype-strict norm-if-expr if-expr)

;; lexicographic not really works here
;; multiply measure of alpha on (sum of beta and gamma), base case 1, this can be falsified
;; need to weigh alpha a little more, add m(alpha) so that it is not equal
;; for fibonacci function, we just need to know the longest depth to prove termination
;; an upper bound for the recursive calls


; the last case is current case + twice of a + whichever branch taken
(definec if-flat-measure (x :if-expr) :nat
  (match x
    (:if-atom 0)
    (('if a b c)
     (+ 1 
        (* 2 (if-flat-measure a))
        (max (if-flat-measure b) (if-flat-measure c))))))

(defthm if-flat-measure-atomic-recurse-b
    (implies (and (if-atomp a)
		  (if-exprp b)
		  (if-exprp c))
     (< (if-flat-measure b)
	(if-flat-measure (list 'if a b c))))
  :hints (("Goal" :in-theory (enable if-flat-measure))))

(defthm if-flat-measure-atomic-recurse-c
  (implies (and (if-atomp a)
                (if-exprp b)
                (if-exprp c))
           (< (if-flat-measure c)
              (if-flat-measure (list 'if a b c))))
  :hints (("Goal" :in-theory (enable if-flat-measure))))

;; Case 2: Pullout transformation decreases measure
(defthm if-flat-measure-pullout-decreases
  (implies (and (if-atomp d)
                (if-atomp e)
                (if-atomp f)
                (if-exprp b)
                (if-exprp c))
           (< (if-flat-measure (list 'if d
                                     (list 'if e b c)
                                     (list 'if f b c)))
              (if-flat-measure (list 'if (list 'if d e f) b c))))
  :hints (("Goal" :in-theory (enable if-flat-measure))))

; check the first element of non-atom, if it is an atom, then recurse
; down to the end to check their conditional position
; if conditional is not atom, then we reconstruct it by first
; putting d at the first conditonal position, which decides
; if we go into e or f, and we put e and f on two branches
; if d is true, then we go into e, whose result should decide
; whether we go into b or c. similarly for f b c statement too
(definec if-flat (x :if-expr) :norm-if-expr
  (declare (xargs :consider-only-ccms ((if-flat-measure x))))
  ;:skip-admissibilityp t
  (match x
    (:if-atom x)
    (('if a b c)
     (match a
       (:if-atom `(if ,a ,(if-flat b) ,(if-flat c)))
       (('if d e f)
        (if-flat `(if ,d (if ,e ,b ,c) (if ,f ,b ,c))))))))

;; match will check each element one by one then use let
;; to record its value

(defdata if-assign (alistof var bool))

(definec lookup-var (var :var a :if-assign) :bool
  (match a
    (nil nil)
    (((!var . val) . &) val)
    (& (lookup-var var (cdr a)))))

(definec lookup-atom (e :if-atom a :if-assign) :bool
  (match e
    (:bool e)
    (& (lookup-var e a))))

(definec if-eval (e :if-expr a :if-assign) :bool
  (match e
    (:if-atom (lookup-atom e a))
    (('if x y z)
     (if (if-eval x a) (if-eval y a) (if-eval z a)))))

;; preclude impossible shape
(defthm impossible-if-condition-shape
  (implies (and (not (consp e3))
                (not (booleanp e3))
                (not (varp e3))
                (consp e4)
                (consp (cdr e4))
                (not (cddr e4)))
           (not (if-exprp (list* 'if e3 e4)))))

;; rewrite rule to use during proof
(property if-flat-equal-if (e :if-expr a :if-assign)
  (== (if-eval e a)
      (if-eval (if-flat e) a)))

(in-theory (disable if-flat-equal-if))

; returns nil when not a bool and can't be found in assignment
(definec assignedp (e :if-atom a :if-assign) :bool
  (or (boolp e)
      (consp (assoc-equal e a))))


(definec validp (e :norm-if-expr a :if-assign) :bool
  (match e
    (:if-atom (lookup-atom e a))
    (('if x y z)
     (if (assignedp x a)
         (if (lookup-atom x a) ; check either branch's validity
             (validp y a)
           (validp z a)) 
       ; check if then branch suppose x is true

       (and (validp y (acons x t a)) 
       ; check if else branch suppose x is nil
            (validp z (acons x nil a)))))))

(definec check-validp (e :if-expr) :bool
  (validp (if-flat e) nil))

;; Main soundness theorem
;; plan:
check-validp e 
=> validp (if-flat e) nil 
=> if-eval (if-flat e) a 
=> if-eval e a 

(definec extend-assign (req :if-assign a :if-assign) :if-assign
  (match req
    (nil a)
    (((k . v) . rst)
     (acons k v (extend-assign rst a)))))

;; if your assignment has an assignment for a variable,
;; adding it does not matter, so collapse to simpler form
(defthm if-eval-acons-same-when-lookup
  (implies (and (if-exprp e)
                (if-assignp a)
                (varp x)
                (booleanp v)
                (equal (lookup-var x a) v))
           (equal (if-eval e (acons x v a))
                  (if-eval e a)))
  :hints (("Goal"
           :in-theory (enable if-eval lookup-atom)
           :induct (if-eval e a))))

;; a more specific form than before
(defthm if-eval-acons-true-when-lookup
  (implies (and (if-exprp e)
                (if-assignp a)
                (varp x)
                (lookup-var x a))
           (equal (if-eval e (acons x t a))
                  (if-eval e a)))
  :hints (("Goal"
           :use ((:instance if-eval-acons-same-when-lookup
                            (e e)
                            (a a)
                            (x x)
                            (v t))))))

;; a specific form like previous
(defthm if-eval-acons-false-when-lookup
  (implies (and (if-exprp e)
                (if-assignp a)
                (varp x)
                (not (lookup-var x a)))
           (equal (if-eval e (acons x nil a))
                  (if-eval e a)))
  :hints (("Goal"
           :use ((:instance if-eval-acons-same-when-lookup
                            (e e)
                            (a a)
                            (x x)
                            (v nil))))))

;; similar to before but in a different form 
(defthm if-eval-cons-cons-true-when-lookup
  (implies (and (if-exprp e)
                (if-assignp a)
                (varp x)
                (lookup-var x a))
           (equal (if-eval e (cons (cons x t) a))
                  (if-eval e a)))
  :hints (("Goal"
           :in-theory (enable acons)
           :use ((:instance if-eval-acons-true-when-lookup
                            (e e)
                            (a a)
                            (x x))))))

;; similar to before
(defthm if-eval-cons-list-false-when-lookup
  (implies (and (if-exprp e)
                (if-assignp a)
                (varp x)
                (not (lookup-var x a)))
           (equal (if-eval e (cons (list x) a))
                  (if-eval e a)))
  :hints (("Goal"
           :in-theory (enable acons)
           :use ((:instance if-eval-acons-false-when-lookup
                            (e e)
                            (a a)
                            (x x))))))

;; similar to before but now adding to assignments
(defthm lookup-var-extend-assign-when-assigned
  (implies (and (varp x)
                (if-assignp req)
                (if-assignp a)
                (consp (assoc-equal x req)))
           (equal (lookup-var x (extend-assign req a))
                  (lookup-var x req)))
  :hints (("Goal"
           :in-theory (enable extend-assign lookup-var)
           :induct (lookup-var x req))))

;; similar 
(defthm lookup-atom-extend-assign-when-assigned
  (implies (and (if-atomp x)
                (if-assignp req)
                (if-assignp a)
                (assignedp x req))
           (equal (lookup-atom x (extend-assign req a))
                  (lookup-atom x req)))
  :hints (("Goal"
           :in-theory (enable assignedp lookup-atom))))

;; if 
(defthm lookup-var-true-preserved-by-extend-assign
  (implies (and (if-assignp req)
                (if-assignp a)
                (varp x)
                (lookup-var x req))
           (lookup-var x (extend-assign req a)))
  :hints (("Goal"
           :in-theory (enable extend-assign lookup-var)
           :induct (extend-assign req a))))

;; if validp says the normalized if-expr is true under req,
;; then adding extensions to it does not change its truth
(defthm validp-sound-on-extend-assign
  (implies (and (norm-if-exprp n)
                (if-assignp req)
                (if-assignp a)
                (validp n req))
           (if-eval n (extend-assign req a)))
  :hints (("Goal"
           :in-theory (enable validp if-eval assignedp lookup-atom extend-assign
                              if-eval-acons-true-when-lookup
                              if-eval-acons-false-when-lookup
                              if-eval-cons-cons-true-when-lookup
                              if-eval-cons-list-false-when-lookup)
           :do-not '(generalize eliminate-destructors fertilize)
           :induct (validp n req))))

;; if normalized n is valid with no assumptions
;; then it evals to true under any assumption
;; logical core
;; need property to show that adding an assignment that
;; agrees with the environment does not change evaluation
;; from this we know that for any (if x y z)
;; if x known true -> check y 
;; if x known false -> check z 
;; if x unknown -> check both branches
(property validp-nil-sound (n :norm-if-expr a :if-assign)
  (implies (validp n nil)
           (if-eval n a))
  :hints (("Goal"
           :in-theory (enable extend-assign)
           :use ((:instance validp-sound-on-extend-assign
                            (n n)
                            (req nil)
                            (a a))))))

;; if the original expr e is valid, then
;; its flattened norm form is valid with no assumption
(defthm check-validp-is-sound-flat
  (implies (and (if-exprp e)
                (if-assignp a)
                (check-validp e))
           (if-eval (if-flat e) a))
  :hints (("Goal"
           :in-theory (enable check-validp)
           :use ((:instance validp-nil-sound
                            (n (if-flat e))
                            (a a))))))

;; if the checker says the formula is valid, formula evaluates to true
;; to prove, we need a theorem that talks about flattened expression
(property check-validp-is-sound (e :if-expr a :if-assign)
  (implies (check-validp e)
           (if-eval e a))
  :hints (("Goal"
           :use ((:instance check-validp-is-sound-flat
                            (e e)
                            (a a))
                 (:instance if-flat-equal-if
                            (e e)
                            (a a))))))

;; Q3f completeness witness
;; proof sketch: 
;; (not (check-validp e))
;; => (not (validp (if-flat e) nil))
;; => (not (if-eval (if-flat e) (counterexample-assign (if-flat e) nil)))
;; => (not (if-eval e (counterexample-assign (if-flat e) nil)))

;; given a normalized expr n and a partial assignment req
;; if validp fails under req 
;; walk through n and extend req only when needed 
;; so that the final assignment makes n eval to false
;; example:
;; (if x true nil) this is not valid 
;; start with empty req, x is not assigned, 
;; validp(true, {x=true}) = true, still valid, try pair x with false 
;; validp(false, {x=false}) = false, find a match that makes it invalid!
;; assign x to false in the req, req = {x=false}
;; return it
(definec counterexample-assign (n :norm-if-expr req :if-assign) :if-assign
  (declare (xargs :consider-only-ccms ((if-flat-measure n))))
  (match n
    ;; reached the end, we have a full witness
    (:if-atom req)
    (('if x y z)
      ; if x is assigned, follow the branch that actually runs
     (if (assignedp x req)
         (if (lookup-atom x req)
             (counterexample-assign y req)
           (counterexample-assign z req))
       ;; if the whole formula is not valid, then at least one branch is not valid 
       ;; under some value of x. try pairing x with true, is it invalid now? if still
       ;; valid, go to the other branch
       (if (not (validp y (acons x t req)))
           (counterexample-assign y (acons x t req))
         (counterexample-assign z (acons x nil req)))))))

;; not shadowing
(defthm lookup-var-acons-diff
  (implies (and (varp x)
                (varp y)
                (booleanp v)
                (if-assignp a)
                (not (equal x y)))
           (equal (lookup-var x (acons y v a))
                  (lookup-var x a)))
  :hints (("Goal"
           :in-theory (enable lookup-var))))

;; counterexample-assign respects existing assignment in req.
(defthm lookup-atom-counterexample-assign-when-assigned
  (implies (and (if-atomp x)
                (norm-if-exprp n)
                (if-assignp req)
                (assignedp x req))
           (equal (lookup-atom x (counterexample-assign n req))
                  (lookup-atom x req)))
  :hints (("Goal"
           :in-theory (enable counterexample-assign assignedp lookup-atom)
           :do-not '(generalize eliminate-destructors fertilize)
           :induct (counterexample-assign n req))))

;; we find an assignment that falsifies the evaluation given that n is not
;; valid with req
;; ban generalize, destructor, and fertilize so that it unfolds as per 
;; the rules of the interpreter not in any algebraic form
(defthm counterexample-assign-falsifies-validp
  (implies (and (norm-if-exprp n)
                (if-assignp req)
                (not (validp n req)))
           (not (if-eval n (counterexample-assign n req))))
  :hints (("Goal"
           :in-theory (enable counterexample-assign validp if-eval assignedp lookup-atom)
           :do-not '(generalize eliminate-destructors fertilize)
           :induct (counterexample-assign n req))))

;; checker works on flattened form
(defthm check-validp-is-complete-flat
  (implies (and (if-exprp e)
                (not (check-validp e)))
           (not (if-eval (if-flat e)
                         (counterexample-assign (if-flat e) nil))))
  :hints (("Goal"
           :in-theory (enable check-validp)
           :use ((:instance counterexample-assign-falsifies-validp
                            (n (if-flat e))
                            (req nil))))))

;; a failure => a counterexample
;; if checker says "NOT valid" => there exists an assignment making it false
;; to prove this, we need:
;; checker works on flattened form 
(property check-validp-is-complete (e :if-expr)
  (let ((a (counterexample-assign (if-flat e) nil)))
    (implies (not (check-validp e))
             (and (if-assignp a)
                  (not (if-eval e a)))))
  :hints (("Goal"
           :use ((:instance check-validp-is-complete-flat
                            (e e))
                 (:instance if-flat-equal-if
                            (e e)
                            (a (counterexample-assign (if-flat e) nil)))))))
