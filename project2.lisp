(in-package "ACL2S")

;; TYPES
;; A type is either a Boolean, an unknown type, or a Function
(defdata ty
  (oneof 'Bool
         (list 'TVar nat)
         (list 'Fun ty ty)))

;; An expression is either True, False, a Variable, A lambda, an Application, and an If expression
(defdata iexpr
  (oneof 'True
         'False
         (list 'Var symbol)
         (list 'Lam symbol iexpr)
         (list 'App iexpr iexpr)
         (list 'If iexpr iexpr iexpr)))

;; Type environment is a mapping from a variable to its type
(defdata tyenv
  (alistof symbol ty))

;; Substitution is a mapping from a variable's id to its type
(defdata subst
  (alistof nat ty))

;; Get the tag off a type
(definec ty-tag (ty0 :ty) :all
  (cond ((equal ty0 'Bool) 'Bool)
        ((and (consp ty0) (equal (car ty0) 'TVar)) 'TVar)
        ((and (consp ty0) (equal (car ty0) 'Fun)) 'Fun)
        (t nil)))

;; Get the Get an variable's id number
(definec tvar-id (ty0 :ty) :all
  (if (and (consp ty0) (equal (car ty0) 'TVar))
      (cadr ty0)
    nil))

;; Get the first part of a function type
(definec fun-dom (ty0 :ty) :all
  (if (and (consp ty0) (equal (car ty0) 'Fun))
      (cadr ty0)
    nil))

;; Get the second part of a function type
(definec fun-cod (ty0 :ty) :all
  (if (and (consp ty0) (equal (car ty0) 'Fun))
      (caddr ty0)
    nil))

;; Create a variable type based on an id number
(definec mk-tvar (n :nat) :ty
  (list 'TVar n))

;; Create a function type based on two types
(definec mk-fun (ty1 :ty ty2 :ty) :ty
  (list 'Fun ty1 ty2))

;; Create an tag for an expression
(definec expr-tag (e :iexpr) :all
  (cond ((equal e 'True) 'True)
        ((equal e 'False) 'False)
        ((consp e) (car e))
        (t nil)))

;; Get the name part of a variable expression
(definec var-name (e :iexpr) :all
  (if (and (consp e) (equal (car e) 'Var))
      (cadr e)
    nil))

;; Get the binding variable part of a lambda
(definec lam-var (e :iexpr) :all
  (if (and (consp e) (equal (car e) 'Lam))
      (cadr e)
    nil))

;; Get the body part of a lambda
(definec lam-body (e :iexpr) :all
  (if (and (consp e) (equal (car e) 'Lam))
      (caddr e)
    nil))

;; Get the function part of an application
(definec app-fun (e :iexpr) :all
  (if (and (consp e) (equal (car e) 'App))
      (cadr e)
    nil))

;; Get the arguments of an application
(definec app-arg (e :iexpr) :all
  (if (and (consp e) (equal (car e) 'App))
      (caddr e)
    nil))

;; Get the condition of an If
(definec if-cond (e :iexpr) :all
  (if (and (consp e) (equal (car e) 'If))
      (cadr e)
    nil))

;; Get the then branch of an If
(definec if-then (e :iexpr) :all
  (if (and (consp e) (equal (car e) 'If))
      (caddr e)
    nil))

;; Get the else branch of an If
(definec if-else (e :iexpr) :all
  (if (and (consp e) (equal (car e) 'If))
      (cadddr e)
    nil))

;; Find the replacement in substitution mapping based on id number
(definec subst-lookup (n :nat s :subst) :all
  (cdr (assoc-equal n s)))

;; Find the type in environment mapping based on its symbol
(definec env-lookup (x :symbol g :tyenv) :all
  (cdr (assoc-equal x g)))

;; apply substitution based on a type's replacement in the mapping
(definec apply-subst-ty (s :subst ty0 :ty) :ty
  (match ty0
    ('Bool 'Bool)
    (('TVar n)
     (let ((hit (subst-lookup n s)))
       (if hit hit ty0)))
    (('Fun ty1 ty2)
     (mk-fun (apply-subst-ty s ty1)
             (apply-subst-ty s ty2)))))

;; update the typing environment recursively until all of tyenv is updated with substitution mapping
(definec apply-subst-env (s :subst g :tyenv) :tyenv
  (if (endp g)
      nil
    (cons (cons (caar g)
                (apply-subst-ty s (cdar g)))
          (apply-subst-env s (cdr g)))))

;; occurs check, important for not going into circle, but forbids recursive type in our type system
;; this is similar to our occurs check in unification algorithm to avoid doing a substitution where left side
;; appears in right side
(definec occurs-in-ty (n :nat ty0 :ty) :bool
  (match ty0
    ('Bool nil)
    (('TVar m) (equal n m))
    (('Fun ty1 ty2)
     (or (occurs-in-ty n ty1)
         (occurs-in-ty n ty2)))))

;; When we have multiple substitution mappings, we need to compose them into a new one
;; This means updating s1's mapping with s2's mapping one by one recursively
;; Warning: This function leads to duplication because we append s2 to whatever we
;; updated with S1
#|
(definec compose-subst (s2 :subst s1 :subst) :subst
  (append
   (if (endp s1)
       nil
     (cons (cons (caar s1)
                 (apply-subst-ty s2 (cdar s1)))
           (compose-subst s2 (cdr s1))))
   s2))
|#

(definec subst-has-keyp (n :nat s :subst) :bool
  (cond
    ((endp s) nil)
    ((equal n (caar s)) t)
    (t (subst-has-keyp n (cdr s)))))

;; in this version, if we find an older binding in s1 have a newer binding in s2, we ignore the s1 part
;; if s2 does not have the same binding, then we keep s1's binding but update s1's right hand side with s2
(definec compose-subst-aux (s2 :subst s1 :subst) :subst
  (cond
    ((endp s1) nil)
    ((subst-has-keyp (caar s1) s2)
     (compose-subst-aux s2 (cdr s1)))
    (t
     (cons (cons (caar s1)
                 (apply-subst-ty s2 (cdar s1)))
           (compose-subst-aux s2 (cdr s1))))))

(definec compose-subst (s2 :subst s1 :subst) :subst
  (append (compose-subst-aux s2 s1)
          s2))

;; check if it is ok substitution
(definec unify-okp (r :all) :bool
  (and (true-listp r)
       (equal (len r) 2)
       (equal (car r) :ok)
       (substp (cadr r))))

;; return the substitution mapping from result of unification
(definec unify-subst (r :all) :subst
  (if (unify-okp r) (cadr r) nil))

;; given a substitution, package it with ok sign
(definec unify-ok (s :subst) :all
  (list :ok s))

;; given a failed unification, package it with fail sign
(definec unify-fail (msg :all) :all
  (list :fail msg))


;; bind a substitution to its label
(definec bind-tvar (n :nat ty0 :ty) :all
  (cond
    ((equal ty0 (mk-tvar n))
     (unify-ok nil))
    ((occurs-in-ty n ty0)
     (unify-fail (list :occurs n ty0)))
    (t
     (unify-ok (list (cons n ty0))))))

(definec unify/fuel (fuel :nat ty1 :ty ty2 :ty) :all
  (if (zp fuel)
      (unify-fail (list :out-of-fuel ty1 ty2))
    (cond
      ;; Two booleans need no unification
      ((and (equal ty1 'Bool)
            (equal ty2 'Bool))
       (unify-ok nil))

      ;; Check if variable has the same type
      ((equal (ty-tag ty1) 'TVar)
       (bind-tvar (tvar-id ty1) ty2))

      ;; Check if variable has the same type
      ((equal (ty-tag ty2) 'TVar)
       (bind-tvar (tvar-id ty2) ty1))

      ;; Unifying two function types
      ;; Unifying the domains first
      ((and (equal (ty-tag ty1) 'Fun)
            (equal (ty-tag ty2) 'Fun))
       (let* ((r1 (unify/fuel (- fuel 1)
                              (fun-dom ty1)
                              (fun-dom ty2))))
         (if (not (unify-okp r1))
             r1
          ;; If domains ok, then unifying the co-domains of functions
           (let* ((s1 (unify-subst r1))
                  (c1 (apply-subst-ty s1 (fun-cod ty1)))
                  (c2 (apply-subst-ty s1 (fun-cod ty2)))
                  (r2 (unify/fuel (- fuel 1) c1 c2)))
             (if (not (unify-okp r2))
                 r2
               (let ((s2 (unify-subst r2)))
                 ;; Finally composing two substitutions from unification
                 (unify-ok (compose-subst s2 s1))))))))

      (t
       (unify-fail (list :mismatch ty1 ty2))))))

(definec unify (ty1 :ty ty2 :ty) :all
  (unify/fuel (+ 1 (acl2-count ty1) (acl2-count ty2)) ty1 ty2))

(definec infer-okp (r :all) :bool
  (and (true-listp r)
       (equal (len r) 4)
       (equal (car r) :ok)
       (substp (cadr r))
       (typ (caddr r))
       (natp (cadddr r))))

;; Get the substitution mapping from an inference
(definec infer-subst (r :all) :subst
  (if (infer-okp r) (cadr r) nil))

;; Get the type from an inference
(definec infer-type (r :all) :ty
  (if (infer-okp r) (caddr r) 'Bool))

;; Get the next from an inference
(definec infer-next (r :all) :nat
  (if (infer-okp r) (cadddr r) 0))

;; Package an inference with ok
(definec infer-ok (s :subst ty0 :ty next :nat) :all
  (list :ok s ty0 next))

;; Package an inference with fail
(definec infer-fail (msg :all) :all
  (list :fail msg))

;; make a new type variable
(definec fresh-tyvar (next :nat) :all
  (list (mk-tvar next) (+ 1 next)))

;; Bool does not need inference
(definec infer-true (g :tyenv e :iexpr next :nat) :all
  (declare (ignorable g e))
  (infer-ok nil 'Bool next))

;; Bool does not need inference
(definec infer-false (g :tyenv e :iexpr next :nat) :all
  (declare (ignorable g e))
  (infer-ok nil 'Bool next))

;; package an inference on variable
(definec infer-var (g :tyenv e :iexpr next :nat) :all
  :ic (equal (expr-tag e) 'Var)
  :skip-body-contractsp t
  (let ((ty0 (env-lookup (var-name e) g)))
    (if ty0
        (infer-ok nil ty0 next)
      (infer-fail (list :unbound-variable (var-name e))))))


(defun infer/fuel (fuel g e next)
  (declare
   (xargs :guard (and (natp fuel)
                      (tyenvp g)
                      (iexprp e)
                      (natp next))
          :measure (nfix fuel)
          :verify-guards nil))
  (if (zp fuel)
      (infer-fail (list :out-of-fuel e))
    (cond
      ((equal (expr-tag e) 'True)
       (infer-true g e next))

      ((equal (expr-tag e) 'False)
       (infer-false g e next))

      ((equal (expr-tag e) 'Var)
       (infer-var g e next))

      ((equal (expr-tag e) 'Lam)
       (let* ((x     (lam-var e))
              (body  (lam-body e))
              (tmp   (fresh-tyvar next))
              (a     (car tmp))
              (next1 (cadr tmp))
              (g1    (cons (cons x a) g))
              (rb    (infer/fuel (- fuel 1) g1 body next1)))
         (if (not (infer-okp rb))
             rb
           (let* ((s1    (infer-subst rb))
                  (tb    (infer-type rb))
                  (next2 (infer-next rb))
                  (a1    (apply-subst-ty s1 a))
                  (tb1   (apply-subst-ty s1 tb)))
             (infer-ok s1 (mk-fun a1 tb1) next2)))))

      ((equal (expr-tag e) 'App)
       (let* ((f  (app-fun e))
              (a  (app-arg e))
              (rf (infer/fuel (- fuel 1) g f next)))
         (if (not (infer-okp rf))
             rf
           (let* ((s1    (infer-subst rf))
                  (tf    (infer-type rf))
                  (next1 (infer-next rf))
                  (g1    (apply-subst-env s1 g))
                  (ra    (infer/fuel (- fuel 1) g1 a next1)))
             (if (not (infer-okp ra))
                 ra
               (let* ((s2    (infer-subst ra))
                      (ta    (infer-type ra))
                      (next2 (infer-next ra))
                      (tmp   (fresh-tyvar next2))
                      (rty   (car tmp))
                      (next3 (cadr tmp))
                      (tf2   (apply-subst-ty s2 tf))
                      (want  (mk-fun ta rty))
                      (ru    (unify tf2 want)))
                 (if (not (unify-okp ru))
                     ru
                   (let* ((s3   (unify-subst ru))
                          (s    (compose-subst s3 (compose-subst s2 s1)))
                          (tres (apply-subst-ty s rty)))
                     (infer-ok s tres next3)))))))))

      ((equal (expr-tag e) 'If)
       (let* ((c   (if-cond e))
              (thn (if-then e))
              (els (if-else e))
              (rc  (infer/fuel (- fuel 1) g c next)))
         (if (not (infer-okp rc))
             rc
           (let* ((s1    (infer-subst rc))
                  (tc    (infer-type rc))
                  (next1 (infer-next rc))
                  (ruc   (unify tc 'Bool)))
             (if (not (unify-okp ruc))
                 ruc
               (let* ((sc    (unify-subst ruc))
                      (s1c   (compose-subst sc s1))
                      (g1    (apply-subst-env s1c g))
                      (rt    (infer/fuel (- fuel 1) g1 thn next1)))
                 (if (not (infer-okp rt))
                     rt
                   (let* ((s2    (infer-subst rt))
                          (tt    (infer-type rt))
                          (next2 (infer-next rt))
                          (g2    (apply-subst-env s2 g1))
                          (re    (infer/fuel (- fuel 1) g2 els next2)))
                     (if (not (infer-okp re))
                         re
                       (let* ((s3    (infer-subst re))
                              (te    (infer-type re))
                              (next3 (infer-next re))
                              (ru    (unify (apply-subst-ty s3 tt) te)))
                         (if (not (unify-okp ru))
                             ru
                           (let* ((s4   (unify-subst ru))
                                  (s    (compose-subst s4
                                                       (compose-subst s3
                                                                      (compose-subst s2 s1c))))
                                  (tout (apply-subst-ty s te)))
                             (infer-ok s tout next3)))))))))))))

      (t
       (infer-fail (list :bad-expression e))))))

(defun infer (g e next)
  (declare
   (xargs :guard (and (tyenvp g) (iexprp e) (natp next))
          :verify-guards nil))
  (infer/fuel (+ 10 (* 4 (acl2-count e))) g e next))

(defun infer-top (e)
  (declare (xargs :guard (iexprp e)
                  :verify-guards nil))
  (infer nil e 0))

;;;; Examples


;; Identity, constant, basic lambdas
;; α  -> α
(infer-top '(Lam x (Var x)))

;; α -> Bool 
(infer-top '(Lam x True))
(infer-top '(Lam x False))

;; assign x to α, y to β
;; inside-out
;; (Lam y (Var x)) gives us β -> α
;; (Lam x (Lam y (Var x))) gives us α -> β -> α 
;; α -> β -> α
;; K Combinator, constant function
(infer-top '(Lam x (Lam y (Var x))))

;; assign x to α, y to β
;; (Lam y (Var y)) gives β -> β
;; (Lam x (Lam y (Var y))) gives α -> β -> β
;; α -> β -> β
(infer-top '(Lam x (Lam y (Var y))))

;; Bool 
(infer-top '(App (Lam x (Var x)) True))
(infer-top '(App (App (Lam x (Lam y (Var x))) True) False))

;; α -> α
(infer-top '(App (Lam f (Lam x (App (Var f) (Var x))))
                 (Lam z (Var z))))


;; Bool
(infer-top '(If True False True))
(infer-top '(If False True False))

;; Bool -> Bool
(infer-top '(Lam x (If (Var x) True False)))
(infer-top '(Lam x (If (Var x) (Var x) False)))

;; Bool -> Bool -> Bool
(infer-top '(Lam x (Lam y (If (Var x) (Var y) True))))

;; α -> α
(infer-top '(Lam f (Var f)))

;; (α -> β) -> α -> β
(infer-top '(Lam f (Lam x (App (Var f) (Var x)))))

;; x is α, g is β, f is γ
;; (App (Var g) (Var x)) gives β = α -> δ, β has to be in this form otherwise this fails
;; (App (Var f (App (Var g) (Var x)))) gives γ = δ -> σ
;; (Lam x (App (Var f (App (Var g) (Var x))))) gives α -> σ
;; (Lam g (Lam x (App (Var f (App (Var g) (Var x)))))) gives β -> (α -> σ)
;; (Lam f (Lam g (Lam x (App (Var f) (App (Var g) (Var x)))))) gives γ -> β -> (α -> σ)
;; which is (δ -> σ) -> (α -> δ) -> (α -> σ)

#|
(:ok ((1 fun (tvar 2) (tvar 3))     ;; replacing β by α -> σ
      (0 fun (tvar 3) (tvar 4))     ;; replacing γ by δ -> σ
      (0 fun (tvar 3) (tvar 4)))    ;; duplicate from compose-subst
;; final result
     (fun (fun (tvar 3) (tvar 4))   ;; (δ -> σ) -> (α -> σ) -> (α -> σ)
          (fun (fun (tvar 2) (tvar 3))
               (fun (tvar 2) (tvar 4))))
     5)
|#


;; (β -> γ) -> (α -> β) -> α -> γ
;; B Combinator, function composition
(infer-top '(Lam f (Lam g (Lam x (App (Var f) (App (Var g) (Var x)))))))

;; (Bool -> α) -> α
(infer-top '(Lam f (App (Var f) True)))

;; (Bool -> α) -> β -> α
(infer-top '(Lam f (Lam x (App (Var f) True))))

;; (α -> β) -> α -> β
(infer-top '(Lam f (Lam x (App (Var f) (Var x)))))

;; (α -> β -> γ) -> β -> α -> γ
;; C Combinator, flip
(infer-top '(Lam f (Lam x (Lam y (App (App (Var f) (Var y)) (Var x))))))

;; (α -> α -> β) -> α -> β
;; W Combinator, duplication
;; assign x to α, f to β
;; (App (Var f) (Var x)) gives β = α -> γ
;; (App (App (Var f) (Var x)) (Var x)) gives γ = α -> δ
;; (Lam x (App (App (Var f) (Var x)) (Var x))) gives α -> δ
;; (Lam f (Lam x (App (App (Var f) (Var x)) (Var x)))) gives α -> γ -> (α -> δ)
;; which can be rewritten as α -> (α -> δ) -> (α -> δ)
(infer-top '(Lam f (Lam x (App (App (Var f) (Var x)) (Var x)))))

;; S Combinator, distribution
;; assign x to α, g to β, f to γ
;; (App (Var f) (Var x)) gives γ = α -> δ
;; (App (Var g) (Var x)) gives β = α -> ε
;; (App (App (Var f) (Var x)) (App (Var g) (Var x))) gives δ = ε -> κ
;; (Lam x (App (App (Var f) (Var x)) (App (Var g) (Var x)))) gives α -> κ
;; (Lam g (Lam x (App (App (Var f) (Var x)) (App (Var g) (Var x))))) gives (α -> ε) -> (α -> κ)
;; (Lam f (Lam g (Lam x (App (App (Var f) (Var x)) (App (Var g) (Var x)))))) gives (α -> δ) -> (α -> ε) -> (α -> κ)
;; which is rewritten as (α -> (ε -> κ)) -> (α -> ε) -> (α -> κ)

(infer-top '(Lam f (Lam g (Lam x (App (App (Var f) (Var x)) (App (Var g) (Var x)))))))

;; Combinator Relations

;; B = S (K S) K

(infer-top '(App
  (App
    (Lam f (Lam g (Lam x (App (App (Var f) (Var x)) (App (Var g) (Var x))))))
    (App
      (Lam x (Lam y (Var x)))
      (Lam f (Lam g (Lam x (App (App (Var f) (Var x)) (App (Var g) (Var x))))))))
  (Lam x (Lam y (Var x)))))


;; C = S (S (K (S (K S) K)) S) (K K)
;; warning: run this leads to stake overflow
#|
(infer-top '(App
  (App
    (Lam f (Lam g (Lam x (App (App (Var f) (Var x)) (App (Var g) (Var x))))))
    (App
      (App
        (Lam f (Lam g (Lam x (App (App (Var f) (Var x)) (App (Var g) (Var x))))))
        (App
          (Lam x (Lam y (Var x)))
          (App
            (App
              (Lam f (Lam g (Lam x (App (App (Var f) (Var x)) (App (Var g) (Var x))))))
              (App
                (Lam x (Lam y (Var x)))
                (Lam f (Lam g (Lam x (App (App (Var f) (Var x)) (App (Var g) (Var x))))))))
            (Lam x (Lam y (Var x))))))
      (Lam f (Lam g (Lam x (App (App (Var f) (Var x)) (App (Var g) (Var x))))))))
  (App
    (Lam x (Lam y (Var x)))
    (Lam x (Lam y (Var x))))))
|#


;; W = S S (S K)
;; Warning: run this leads to stake overflow
#|
(infer-top '(App
  (App
    (Lam f (Lam g (Lam x (App (App (Var f) (Var x)) (App (Var g) (Var x))))))
    (Lam f (Lam g (Lam x (App (App (Var f) (Var x)) (App (Var g) (Var x)))))))
  (App
    (Lam f (Lam g (Lam x (App (App (Var f) (Var x)) (App (Var g) (Var x))))))
    (Lam x (Lam y (Var x))))))
|#




;; unbound variable
(infer-top '(Var x))
(infer-top '(Lam x (Var y)))

;; applying non-function
(infer-top '(App True False))
(infer-top '(Lam x (App True (Var x))))

;; Our type system (and HM too) cannot handle heterogenous if branches
(infer-top '(If True False (Lam x True)))
(infer-top '(If True (Lam x True) False))



;; Bad If Condition
(infer-top '(If (Lam x True) False True))

;; Our type system cannot handle infinite (recursive) type 
(infer-top '(Lam x (App (Var x) (Var x))))
(infer-top '(Lam f (Lam x (App (Var f) (Var f)))))
