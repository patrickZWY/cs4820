(in-package "ACL2S")

;; TYPES
(defdata ty
  (oneof 'Bool
         (list 'TVar nat)
         (list 'Fun ty ty)))

(defdata iexpr
  (oneof 'True
         'False
         (list 'Var symbol)
         (list 'Lam symbol iexpr)
         (list 'App iexpr iexpr)
         (list 'If iexpr iexpr iexpr)))

(defdata tyenv
  (alistof symbol ty))

(defdata subst
  (alistof nat ty))

(definec ty-tag (ty0 :ty) :all
  (cond ((equal ty0 'Bool) 'Bool)
        ((and (consp ty0) (equal (car ty0) 'TVar)) 'TVar)
        ((and (consp ty0) (equal (car ty0) 'Fun)) 'Fun)
        (t nil)))

(definec tvar-id (ty0 :ty) :all
  (if (and (consp ty0) (equal (car ty0) 'TVar))
      (cadr ty0)
    nil))

(definec fun-dom (ty0 :ty) :all
  (if (and (consp ty0) (equal (car ty0) 'Fun))
      (cadr ty0)
    nil))

(definec fun-cod (ty0 :ty) :all
  (if (and (consp ty0) (equal (car ty0) 'Fun))
      (caddr ty0)
    nil))

(definec mk-tvar (n :nat) :ty
  (list 'TVar n))

(definec mk-fun (ty1 :ty ty2 :ty) :ty
  (list 'Fun ty1 ty2))

(definec expr-tag (e :iexpr) :all
  (cond ((equal e 'True) 'True)
        ((equal e 'False) 'False)
        ((consp e) (car e))
        (t nil)))

(definec var-name (e :iexpr) :all
  (if (and (consp e) (equal (car e) 'Var))
      (cadr e)
    nil))

(definec lam-var (e :iexpr) :all
  (if (and (consp e) (equal (car e) 'Lam))
      (cadr e)
    nil))

(definec lam-body (e :iexpr) :all
  (if (and (consp e) (equal (car e) 'Lam))
      (caddr e)
    nil))

(definec app-fun (e :iexpr) :all
  (if (and (consp e) (equal (car e) 'App))
      (cadr e)
    nil))

(definec app-arg (e :iexpr) :all
  (if (and (consp e) (equal (car e) 'App))
      (caddr e)
    nil))

(definec if-cond (e :iexpr) :all
  (if (and (consp e) (equal (car e) 'If))
      (cadr e)
    nil))

(definec if-then (e :iexpr) :all
  (if (and (consp e) (equal (car e) 'If))
      (caddr e)
    nil))

(definec if-else (e :iexpr) :all
  (if (and (consp e) (equal (car e) 'If))
      (cadddr e)
    nil))

(definec subst-lookup (n :nat s :subst) :all
  (cdr (assoc-equal n s)))

(definec env-lookup (x :symbol g :tyenv) :all
  (cdr (assoc-equal x g)))

(definec apply-subst-ty (s :subst ty0 :ty) :ty
  (match ty0
    ('Bool 'Bool)
    (('TVar n)
     (let ((hit (subst-lookup n s)))
       (if hit hit ty0)))
    (('Fun ty1 ty2)
     (mk-fun (apply-subst-ty s ty1)
             (apply-subst-ty s ty2)))))

(definec apply-subst-env (s :subst g :tyenv) :tyenv
  (if (endp g)
      nil
    (cons (cons (caar g)
                (apply-subst-ty s (cdar g)))
          (apply-subst-env s (cdr g)))))

(definec occurs-in-ty (n :nat ty0 :ty) :bool
  (match ty0
    ('Bool nil)
    (('TVar m) (equal n m))
    (('Fun ty1 ty2)
     (or (occurs-in-ty n ty1)
         (occurs-in-ty n ty2)))))

(definec compose-subst (s2 :subst s1 :subst) :subst
  (append
   (if (endp s1)
       nil
     (cons (cons (caar s1)
                 (apply-subst-ty s2 (cdar s1)))
           (compose-subst s2 (cdr s1))))
   s2))

(definec unify-okp (r :all) :bool
  (and (true-listp r)
       (equal (len r) 2)
       (equal (car r) :ok)
       (substp (cadr r))))

(definec unify-subst (r :all) :subst
  (if (unify-okp r) (cadr r) nil))

(definec unify-ok (s :subst) :all
  (list :ok s))

(definec unify-fail (msg :all) :all
  (list :fail msg))



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
      ((and (equal ty1 'Bool)
            (equal ty2 'Bool))
       (unify-ok nil))

      ((equal (ty-tag ty1) 'TVar)
       (bind-tvar (tvar-id ty1) ty2))

      ((equal (ty-tag ty2) 'TVar)
       (bind-tvar (tvar-id ty2) ty1))

      ((and (equal (ty-tag ty1) 'Fun)
            (equal (ty-tag ty2) 'Fun))
       (let* ((r1 (unify/fuel (- fuel 1)
                              (fun-dom ty1)
                              (fun-dom ty2))))
         (if (not (unify-okp r1))
             r1
           (let* ((s1 (unify-subst r1))
                  (c1 (apply-subst-ty s1 (fun-cod ty1)))
                  (c2 (apply-subst-ty s1 (fun-cod ty2)))
                  (r2 (unify/fuel (- fuel 1) c1 c2)))
             (if (not (unify-okp r2))
                 r2
               (let ((s2 (unify-subst r2)))
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

(definec infer-subst (r :all) :subst
  (if (infer-okp r) (cadr r) nil))

(definec infer-type (r :all) :ty
  (if (infer-okp r) (caddr r) 'Bool))

(definec infer-next (r :all) :nat
  (if (infer-okp r) (cadddr r) 0))

(definec infer-ok (s :subst ty0 :ty next :nat) :all
  (list :ok s ty0 next))

(definec infer-fail (msg :all) :all
  (list :fail msg))

(definec fresh-tyvar (next :nat) :all
  (list (mk-tvar next) (+ 1 next)))

(definec infer-true (g :tyenv e :iexpr next :nat) :all
  (declare (ignorable g e))
  (infer-ok nil 'Bool next))

(definec infer-false (g :tyenv e :iexpr next :nat) :all
  (declare (ignorable g e))
  (infer-ok nil 'Bool next))

(definec infer-var (g :tyenv e :iexpr next :nat) :all
  :ic (equal (expr-tag e) 'Var)
  :skip-body-contractsp t
  (let ((ty0 (env-lookup (var-name e) g)))
    (if ty0
        (infer-ok nil ty0 next)
      (infer-fail (list :unbound-variable (var-name e))))))

;; replace the whole mutual-recursion block with this

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

(infer-top '(Lam x (Var x)))
(infer-top '(Lam x True))
(infer-top '(App (Lam x (Var x)) True))
(infer-top '(If True False True))
(infer-top '(Lam x (App (Var x) (Var x))))