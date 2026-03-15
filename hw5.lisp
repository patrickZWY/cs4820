(load "~/quicklisp/setup.lisp")

(ql:quickload :trivia)
(ql:quickload :cl-ppcre)
(ql:quickload :let-plus)

(setf ppcre:*allow-named-registers* t)
(defpackage :tp (:use :cl :trivia :ppcre :let-plus :acl2 :acl2s))
(in-package :tp)

(import 'acl2s-interface-internal::(acl2s-compute acl2s-query))

;; sink, fast judgement, see nil in and, directly nil, see true in or directly true
;; idempotent only for and/or because they reflect info and not changes anything
;; true with and does not change anything, nil with or does not change anything, similar for iff and xor
;; 
(defparameter *p-ops*
  '((and     :arity - :identity t   :idem t   :sink nil)
    (or      :arity - :identity nil :idem t   :sink t)
    (not     :arity 1 :identity -   :idem nil :sink -)
    (implies :arity 2 :identity -   :idem nil :sink -)
    (iff     :arity - :identity t   :idem nil :sink -)
    (xor     :arity - :identity nil :idem nil :sink -)
    (if      :arity 3 :identity -   :idem nil :sink -)))

; p-fun is a list of operator names
(defparameter *p-funs* (mapcar #'car *p-ops*))

; reload function for convenience
; call with (tp::r)
(defun r ()
    (load "hw5.lisp"))

;; find if a occurs in x with structure equality
;; #' is treating function as argument
;; :test #'equal
(defun in (a x)
  (member a x :test #'equal))

;; l is being evaluated with the ,
(defmacro len (l) `(length ,l))

(defun p-funp (x)
  (in x *p-funs*))

;; find the pair that matches key k in association list l
;; return first the part after the operator name then the whole thing
(defun key-alist->val (k l)
  (let* ((in (assoc k l :test #'equal)))
    (values (cdr in) in)))

(key-alist->val 'iff *p-ops*)

;; get the rest of the list from the point of k in list l
;; return first the second one from the point on
;; then return the whole result
(defun key-list->val (k l)
  (let* ((in (member k l :test #'equal)))
    (values (cadr in) in)))

;; we can use these two functions to search the parameter of each operator
;; return first the arity number then return the whole thing after name 'arity
(key-list->val ':arity  (key-alist->val 'iff *p-ops*))

;; similarly, return first the parameter given the key name
;; then return the whole thing after name 'key
(defun pfun-key->val (fun key)
  (key-list->val key (key-alist->val fun *p-ops*)))

(defun remove-dups (l)
  (remove-duplicates l :test #'equal))

(defmacro == (x y) `(equal ,x ,y))
(defmacro != (x y) `(not (equal ,x ,y)))

(defparameter *booleans* '(t nil))

(defun booleanp (x)
  (in x *booleans*))

;; if operator is matched, then args are sent here to check if they
;; match the format for specific operator
(defun pfun-argsp (pop args)
  (and (p-funp pop)
        ;; arity only takes the first value and throws away the second
       (let ((arity (key-list->val :arity (key-alist->val pop *p-ops*))))
         (and (or (== arity '-)
                  (== (len args) arity))
              ;; every arg has to be a propositional formula
              (every #'p-formulap args)))))


(defun p-formulap (f)
  (match f
    ((type boolean) t) ; don't need this case, but here for emphasis
    ((type symbol) t)
    ((list* pop args)
     (if (p-funp pop)
         (pfun-argsp pop args)
       t))
    (_ nil)))


(assert (p-formulap '(and)))
(assert (p-formulap '(and x y z)))
(assert (p-formulap '(and t nil)))
(assert (not (p-formulap '(implies x t nil))))
(assert (p-formulap 'q))
(assert (p-formulap '(implies (foo x) (bar y))))
(assert (p-formulap '(iff p q r s t)))
(assert (p-formulap '(xor p q r s t)))
(assert (not (p-formulap '(if p q r t))))

;; this pre-process and packages each arg by sending each
;; one by one to p-skeleton
;; stich them up back with the rest of the formula then keep going
;; until all args are exhausted
;; &values bind multiple values returned from the p-skeleton computation
(defun p-skeleton-args (args amap acc)
  (if (endp args)
      (values (reverse acc) amap)
    (let+ (((&values na namap)
            (p-skeleton (car args) amap)))
          (p-skeleton-args (cdr args) namap (cons na acc)))))

;; take in a formula and an optional map
;; if symbol, return unchanged
;; if one of the operators match, then 
(defun p-skeleton (f &optional amap) ;amap is nil if not specified
  (match f
    ((type symbol) (values f amap))
    ((list* pop args)
     (if (p-funp pop)
          ;; recurse into args if ops
          ;; for each arg, send it to p-skeleton-args
          ;; which produces updated formula and map by sending back here
          ;; then send the finished results back to stick back to other parts
          ;; and keep dealing with args until all args are exhausted
         (let+ (((&values nargs namap)
                 (p-skeleton-args args amap nil)))
               (values (cons pop nargs) namap))
       ;; then it is atomic values, reuse or create a substitution
       (let ((geta (key-alist->val f amap)))
         (if geta
             (values geta amap)
           (let ((gen (gentemp "P")))
             (values gen (acons f gen amap)))))))
    (_ (error "Not a p-formula"))))


(p-skeleton
 '(or p q r s))

(p-skeleton
 '(iff q r))

(p-skeleton
 '(or p (iff q r)))

(p-skeleton
 '(or p (iff q r) (and p q p) (if p (and p q) (or p q))))

(p-skeleton
 '(iff p p q (foo t nil) (foo t nil) (or p q)))

(p-skeleton
 '(xor p p q (foo t nil) (foo t nil) (or p q)))

(p-skeleton
 '(iff p p q (foo t r) (foo s nil) (or p q)))

(p-skeleton
 '(or (foo a (g a c)) (g a c) (not (foo a (g a c)))))


(defun nary-to-2ary (fun args)
  ;; get the identity parameter from prop op
  (let ((identity (pfun-key->val fun :identity)))
    (match args
      (nil identity)
      ;; single element just return
      ((list x) (to-acl2s x))
      ;; otherwise make them into 2ary 
      (_ (acl2s::xxxjoin (to-acl2s fun) (mapcar #'to-acl2s args))))))

(defun to-acl2s (f)
  ;; replace the atoms
  (let ((s (p-skeleton f)))
    (match s
      ((type symbol) (intern (symbol-name f) "ACL2S"))
      ((cons x xs)
       (if (in x '(iff xor))
           (nary-to-2ary x xs)
         (mapcar #'to-acl2s f)))
      (_ f))))

(to-acl2s '(and a b c d))
(to-acl2s '(iff a b c d))
(to-acl2s '(xor a b c d))

(defun pvars- (f)
  (match f
    ((type boolean) nil)
    ((type symbol) (list f))
    ((list* op args)
     (and (p-funp op)
          (reduce #'append (mapcar #'pvars- args))))))

(defun pvars (f) (remove-dups (pvars- f)))

(pvars '(and t (iff nil) (iff t nil t nil) p q))
(pvars '(iff p p q (foo t r) (foo s nil) (or p q)))
(pvars '(if p q (or r (foo t s) (and (not q)))))

(defun boolean-hyps (l)
  (reduce #'append
          (mapcar #'(lambda (x) `(,x :bool))
                  (mapcar #'to-acl2s l))))

(boolean-hyps '(p q r))

;; put f and g into iff form, call it iff
;; get rid of non-prop atoms, call it siff
(defun acl2s-check-equal (f g)
  (let* ((iff `(iff ,f ,g))
         (siff (p-skeleton iff))
  ;; collect all vars we need to quantify over
	 (pvars (pvars siff))
   ;; convert to acl2s format 
	 (aiff (to-acl2s siff))
        ;; left side of iff
         (af (second aiff))
         ;; right side of iff
         (ag (third aiff))
         ;; mark bools for booleans
         (bhyps (boolean-hyps pvars)))
    (acl2s-query
     `(acl2s::property ,bhyps (acl2s::iff ,af ,ag)))))

;; And some simple examples.
(acl2s-check-equal 'p 'p)
(acl2s-check-equal 'p 'q)

; Here is how to check if the query succeeded
(assert (== (car (acl2s-check-equal 'p 'p)) nil))

; So, here's a useful function
(defun assert-acl2s-equal (f g)
  (assert (== (car (acl2s-check-equal f g)) nil)))

(assert-acl2s-equal 'p 'p)
;; False Statement
;; (assert-acl2s-equal 'p 'q)


(let* ((x '(or (foo a (g a c)) (g a c) (not (foo a (g a c))))))
  (assert-acl2s-equal x t))

(let* ((x '(or (foo a (g a c)) (g a c) (not (foo a (g a c)))))
       (sx (p-skeleton x)))
  (assert-acl2s-equal sx t))


#|

 Question 1. (25 pts)

|#


(defun opposite-literal-p (x y)
  (or (equal x `(not ,y))
      (equal y `(not ,x))))

(defun zero-one-arity (op args)
  (cond
    ((equal op 'and)
     (cond ((endp args) t)
           ((endp (cdr args)) (car args))
           (t (cons op args))))
    ((equal op 'or)
     (cond ((endp args) nil)
           ((endp (cdr args)) (car args))
           (t (cons op args))))
    ((equal op 'iff)
     (cond ((endp args) t)
           ((endp (cdr args)) (car args))
           (t (cons op args))))
    ((equal op 'xor)
     (cond ((endp args) nil)
           ((endp (cdr args)) (car args))
           (t (cons op args))))
    (t (cons op args))))

(defun arbitrary-arity (op args)
  (if (in op '(and or iff xor))
      (cons op
            (mapcan #'(lambda (x)
                        (match x
                          ((type boolean) (list x))
                          ((type symbol) (list x))
                          ((list* op2 args2)
                           (if (equal op2 op) args2 (list x)))
                          (_ (list x))))
                    args))
    (cons op args)))

(defun reduce-sink (op args)
  (match op
    ('and (if (in nil (remove-if-not #'booleanp args)) nil (cons op args)))
    ('or  (if (in t (remove-if-not #'booleanp args)) t (cons op args)))
    (_ (cons op args))))

(defun reduce-constants (op args)
  (match op
    ('and (cons op (remove t args :test #'equal)))
    ('or  (cons op (remove nil args :test #'equal)))
    (_ (cons op args))))

(defun reduce-double (op args)
  (if (equal op 'not)
      (let ((x (car args)))
        (match x
          ((list 'not inner) inner)
          ((list* 'iff rest) (cons 'xor rest))
          ((list* 'xor rest) (cons 'iff rest))
          (_ (cons op args))))
    (cons op args)))

(defun reduce-repetition (op args)
  (if (pfun-key->val op :idem)
      (cons op (remove-dups args))
    (cons op args)))

(defun reduce-opposite (op args)
  (match op
    ('and
     (if (some #'(lambda (x)
                   (some #'(lambda (y) (opposite-literal-p x y)) args))
               args)
         nil
       (cons op args)))
    ('or
     (if (some #'(lambda (x)
                   (some #'(lambda (y) (opposite-literal-p x y)) args))
               args)
         t
       (cons op args)))
    (_ (cons op args))))

(defun reduce-shannon (op args)
  (if (and (equal op 'and)
           (some #'atom args)
           (some #'consp args)
           (every #'(lambda (x)
                      (or (atom x)
                          (and (consp x)
                               (equal (car x) 'or))))
                  args))
      (let* ((singletons (remove-if-not #'atom args))
             (or-args (mapcar #'cdr (remove-if #'atom args)))
             (common (if (endp or-args)
                         singletons
                       (reduce #'(lambda (a b)
                                   (intersection a b :test #'equal))
                               or-args
                               :initial-value singletons))))
        (if (endp common)
            (cons op args)
            (car common)))
    (cons op args)))

(defun apply-reduction (fn f)
  (if (consp f)
      (funcall fn (car f) (cdr f))
    f))

(defun p-simplify-once (f)
  (match f
    ((type boolean) f)
    ((type symbol) f)
    ((list* op args)
     (if (not (p-funp op))
         f
       (let* ((simplified-args (mapcar #'p-simplify-once args))
              (f1 (arbitrary-arity op simplified-args))
              (f2 (apply-reduction #'zero-one-arity f1))
              (f3 (if (consp f2) (apply-reduction #'reduce-sink f2) f2))
              (f4 (if (consp f3) (apply-reduction #'reduce-constants f3) f3))
              (f5 (if (consp f4) (apply-reduction #'reduce-double f4) f4))
              (f6 (if (consp f5) (apply-reduction #'reduce-repetition f5) f5))
              (f7 (if (consp f6) (apply-reduction #'reduce-opposite f6) f6))
              (f8 (if (consp f7) (apply-reduction #'reduce-shannon f7) f7))
              (f9 (if (consp f8) (apply-reduction #'zero-one-arity f8) f8))
              (f10 (if (consp f9) (apply-reduction #'reduce-double f9) f9)))
         f10)))
    (_ (error "Not a p-formula"))))

(defun p-simplify (f)
  (let ((result (p-simplify-once f)))
    (if (equal result f)
        result
      (p-simplify result))))

(assert (equal (zero-one-arity 'and '()) t))
(assert (equal (zero-one-arity 'or '()) nil))
(assert (equal (zero-one-arity 'iff '()) t))
(assert (equal (zero-one-arity 'xor '()) nil))

(assert (equal (zero-one-arity 'and '(p)) 'p))
(assert (equal (zero-one-arity 'or '(p)) 'p))
(assert (equal (zero-one-arity 'iff '(p)) 'p))
(assert (equal (zero-one-arity 'xor '(p)) 'p))

(assert (equal (arbitrary-arity 'and '(p q (and r s))) '(and p q r s)))
(assert (equal (arbitrary-arity 'or '(p q (or r s))) '(or p q r s)))
(assert (equal (arbitrary-arity 'iff '(p q (iff r s))) '(iff p q r s)))
(assert (equal (arbitrary-arity 'xor '(p q (xor r s))) '(xor p q r s)))

(assert (equal (reduce-sink 'and '(p q nil)) nil))
(assert (equal (reduce-sink 'or '(p q t)) t))

(assert (equal (reduce-constants 'and '(t x y)) '(and x y)))
(assert (equal (reduce-constants 'or '(nil x y)) '(or x y)))

(assert (equal (reduce-double 'not '((not x))) 'x))
(assert (equal (reduce-double 'not '((iff x y))) '(xor x y)))
(assert (equal (reduce-double 'not '((xor x y))) '(iff x y)))

(assert (equal (reduce-repetition 'and '(x y x z)) '(and y x z)))
(assert (equal (reduce-repetition 'or '(x y x z)) '(or y x z)))
(assert (equal (reduce-repetition 'xor '(x y x)) '(xor x y x)))

(assert (equal (reduce-opposite 'or '(x y (not x) z)) t))
(assert (equal (reduce-opposite 'and '(x y (not x) z)) nil))

(assert (equal (reduce-shannon 'and '((or p q) (or r q p) p)) 'p))
(assert (equal (reduce-shannon 'and '((or p q) (or r q p) q)) 'q))

(assert-acl2s-equal
 (p-simplify '(and p t (foo t nil) q))
 '(and p (foo t nil) q))

(assert-acl2s-equal
 (p-simplify '(and p t (foo t b) nil))
 nil)

(assert-acl2s-equal
 (p-simplify '(or nil p q))
 '(or p q))

(assert-acl2s-equal
 (p-simplify '(and p q (and r s) (or u v)))
 '(and p q r s (or u v)))

(assert-acl2s-equal
 (p-simplify '(and))
 t)

(assert-acl2s-equal
 (p-simplify '(or))
 nil)

(assert-acl2s-equal
 (p-simplify '(iff))
 t)

(assert-acl2s-equal
 (p-simplify '(xor))
 nil)

(assert-acl2s-equal
 (p-simplify '(and p nil q))
 nil)

(assert-acl2s-equal
 (p-simplify '(or p t q))
 t)

(assert-acl2s-equal
 (p-simplify '(not (not p)))
 'p)

(assert-acl2s-equal
 (p-simplify '(not (iff p q)))
 '(xor p q))

(assert-acl2s-equal
 (p-simplify '(not (xor p q)))
 '(iff p q))

(assert-acl2s-equal
 (p-simplify '(and (or p q) (or r q p) p))
 'p)

(assert-acl2s-equal
 (p-simplify '(or x y (foo a b) z (not (foo a b)) w))
 t)

(assert-acl2s-equal
 (p-simplify '(and p q p r q))
 '(and p q r))

(assert-acl2s-equal
 (p-simplify '(and p q (not p) r))
 nil)

(assert-acl2s-equal 
 (p-simplify '(and p (or nil x (and q q)) (not (not r)))) 
 '(and p (or x q) r))

(assert-acl2s-equal
 (p-simplify '(iff p (xor q (not (not q))) (and r t) (or s nil)))
 '(iff p (xor q q) r s))

;; generate fresh variable starting from P_0 
(defun tseitin-var (n)
  (intern (format nil "P_~A" n) *package*))

;; create negation of a formula
(defun tseitin-neg (x)
  (match x
    ((list 'not y) y)
    (_ `(not ,x))))

;; basic unit of CNF
(defun tseitin-clause (&rest lits)
  (cons 'or lits))

;; final form of CNF
(defun tseitin-conj (clauses top)
  (cons 'and (append clauses (list top))))

;; fm has tseitin variable in defs
;; defs is a lookup table for caching
(defun tseitin-lookup (fm defs)
  (cdr (assoc fm defs :test #'equal)))

;; rewrite iff into more primitive forms
;; for more than two arguments, zip it
(defun iff-chain-form (args)
  (match args
    (nil t)
    ((list x) x)
    ((list x y)
     `(or (and ,x ,y)
          (and (not ,x) (not ,y))))
    (_
     `(and ,@(mapcar #'(lambda (pair)
                         (iff-chain-form pair))
                     (mapcar #'list args (cdr args)))))))

;; xor of 2 args
(defun xor2-form (x y)
  `(or (and ,x (not ,y))
       (and (not ,x) ,y)))

;; general xor transformer
;; more than 2 become nested xors
(defun xor-chain-form (args)
  (match args
    (nil nil)
    ((list x) x)
    ((list x y) (xor2-form x y))
    (_ (xor2-form (car args)
                  (xor-chain-form (cdr args))))))

;; negation step in tseitin
(defun tseitin-not-clauses (p x)
  ;; p <-> (not x)
  (list (tseitin-clause (tseitin-neg p) (tseitin-neg x))
        (tseitin-clause x p)))

;; when subformula is and clause
;; <- direction negate the lits
;; -> direction negate the p, distribute to each of lit
(defun tseitin-and-clauses (p lits)
  ;; p <-> (and lits)
  (append
   (mapcar #'(lambda (x)
               (tseitin-clause (tseitin-neg p) x))
           lits)
   (list (apply #'tseitin-clause
                (cons p (mapcar #'tseitin-neg lits))))))

;; when subforumula is or clause
;; <- direction negate the lits, distribute to p
;; -> direction negate the p
(defun tseitin-or-clauses (p lits)
  ;; p <-> (or lits)
  (append
   (list (apply #'tseitin-clause
                (cons (tseitin-neg p) lits)))
   (mapcar #'(lambda (x)
               (tseitin-clause p (tseitin-neg x)))
           lits)))

;; send formula to different destinations
;; based on their operator
(defun tseitin-def-clauses (fm p)
  (match fm
    ((list 'not x)
     (tseitin-not-clauses p x))
    ((list* 'and args)
     (tseitin-and-clauses p args))
    ((list* 'or args)
     (tseitin-or-clauses p args))
    (_
     (error "Unsupported stored Tseitin definition: ~a" fm))))

;; return
;; rep : a list of representatives for the arguments
;; defs : definitions table for cached results
;; n : counter
(defun tseitin-main-list (args defs n acc)
  (if (endp args)
      (values (reverse acc) defs n)
    (let+ (((&values rep defs1 n1)
            (tseitin-main (car args) defs n)))
      (tseitin-main-list (cdr args) defs1 n1 (cons rep acc)))))

;; reuse existing representative
;; or
;; create a new var and update cached result
(defun tseitin-introduce (fm defs n)
  (let ((old (tseitin-lookup fm defs)))
    (if old
        (values old defs n)
      (let ((v (tseitin-var n)))
        (values v
                (acons fm v defs)
                (+ n 1))))))

;; walk the formula and return
;; representative 
;; defs cached results
;; next counter
(defun tseitin-main (f defs n)
  ;; returns representative, defs, next-counter
  (match f
    ((type boolean)
     (values f defs n))

    ((type symbol)
     (values f defs n))

    ((list 'not x)
     (let+ (((&values rx defs1 n1)
             (tseitin-main x defs n)))
       (tseitin-introduce `(not ,rx) defs1 n1)))

    ((list* 'and args)
     (let+ (((&values reps defs1 n1)
             (tseitin-main-list args defs n nil)))
       (tseitin-introduce (cons 'and reps) defs1 n1)))

    ((list* 'or args)
     (let+ (((&values reps defs1 n1)
             (tseitin-main-list args defs n nil)))
       (tseitin-introduce (cons 'or reps) defs1 n1)))

    ((list 'implies a b)
     (tseitin-main `(or (not ,a) ,b) defs n))

    ((list 'if a b c)
     (tseitin-main `(or (and ,a ,b)
                        (and (not ,a) ,c))
                   defs n))

    ((list* 'iff args)
     (tseitin-main (iff-chain-form args) defs n))

    ((list* 'xor args)
     (tseitin-main (xor-chain-form args) defs n))

    (_
     (values f defs n))))

;; transform the caching table into cnf clauses
(defun tseitin-defs->clauses (defs)
  (mapcan #'(lambda (pr)
              (tseitin-def-clauses (car pr) (cdr pr)))
          defs))

(defun tseitin (f)
  (let* ((sf (p-simplify f)))
    (if (booleanp sf)
        sf
      (let+ (((&values sk _) (p-skeleton sf))
             ((&values top defs _) (tseitin-main sk nil 0)))
        (tseitin-conj (tseitin-defs->clauses (reverse defs)) top)))))

(defun clause-lits (f)
    (match f
        ((list* 'or lits) lits)
        (_ (list f))))

(defun cnf-clauses (f)
    (match f
        ((list* 'and clauses) clauses)
         (_ (list f))))

(defun all-lits (f)
    (reduce #'append
        (mapcar #'clause-lits (cnf-clauses f))
            :initial-value nil))

(defun unit-clause-p (c)
  (equal (len (clause-lits c)) 1))

(defun one-literal-rule (f)
  (let* ((clauses (cnf-clauses f))
         (unit (car (remove-if-not #'unit-clause-p clauses))))
    (if (null unit)
        f
      (let* ((u (car (clause-lits unit)))
             (u1 (tseitin-neg u))
             (c (remove-if #'(lambda (x)
                               (in u (clause-lits x)))
                           clauses))
             (c1 (mapcar #'(lambda (y)
                             (zero-one-arity
                              'or
                              (remove u1 (clause-lits y) :test #'equal)))
                         c)))
        (zero-one-arity 'and c1)))))


(defun pure-literal (f)
    (let ((lits (remove-dups (all-lits f))))
        (car (remove-if #'(lambda (x)
                                (in (tseitin-neg x) lits))
                                lits))))

(defun remove-clauses-with-lit (lit clauses)
    (remove-if #'(lambda (c)
                    (in lit (clause-lits c)))
                clauses))

(defun pure-literal-rule (f)
  (let* ((clauses (cnf-clauses f))
         (lit (pure-literal f)))
    (if (null lit)
        f
      (let ((new-clauses (remove-clauses-with-lit lit clauses)))
        (zero-one-arity 'and new-clauses)))))


(defun resolve-rule (var c1 c2)
  (cond
    ((and (in var (clause-lits c1))
          (in (tseitin-neg var) (clause-lits c2)))
     (let* ((l1 (remove var (clause-lits c1) :test #'equal))
            (l2 (remove (tseitin-neg var) (clause-lits c2) :test #'equal))
            (res (remove-dups (append l1 l2))))
       (zero-one-arity 'or res)))
    ((and (in (tseitin-neg var) (clause-lits c1))
          (in var (clause-lits c2)))
     (let* ((l1 (remove (tseitin-neg var) (clause-lits c1) :test #'equal))
            (l2 (remove var (clause-lits c2) :test #'equal))
            (res (remove-dups (append l1 l2))))
       (zero-one-arity 'or res)))
    (t nil)))


(defun clause-has-lit-p (lit c)
  (in lit (clause-lits c)))

(defun tautologyp (c)
  (let ((lits (clause-lits c)))
    (some #'(lambda (x)
              (in (tseitin-neg x) lits))
          lits)))

(defun resolve-all-pairs (var pos neg)
  (remove-dups
   (remove nil
           (mapcan #'(lambda (c1)
                       (mapcar #'(lambda (c2)
                                   (let ((r (resolve-rule var c1 c2)))
                                     (if (and r (not (tautologyp r)))
                                         r
                                       nil)))
                               neg))
                   pos))))

(defun remove-var-clauses (var clauses)
  (remove-if #'(lambda (c)
                 (or (clause-has-lit-p var c)
                     (clause-has-lit-p (tseitin-neg var) c)))
             clauses))

(defun dp-step (var f)
  (let* ((clauses (cnf-clauses f))
         (pos (remove-if-not #'(lambda (c)
                                 (clause-has-lit-p var c))
                             clauses))
         (neg (remove-if-not #'(lambda (c)
                                 (clause-has-lit-p (tseitin-neg var) c))
                             clauses))
         (rest (remove-var-clauses var clauses))
         (resolvents (resolve-all-pairs var pos neg))
         (new-clauses (append rest resolvents)))
    (zero-one-arity 'and new-clauses)))

(assert-acl2s-equal
 (dp-step 'p '(and (or p q) (or (not p) r)))
 '(or q r))

(assert-acl2s-equal
 (dp-step 'p '(and (or p q) (or (not p) r) (or s t)))
 '(and (or s t) (or q r)))

(assert-acl2s-equal
 (dp-step 'p '(and p (or (not p) r)))
 'r)

(assert-acl2s-equal
 (dp-step 'p '(and (or p q) (not p)))
 'q)

(assert-acl2s-equal
 (dp-step 'p
          '(and (or p q)
                (or p r)
                (or (not p) s)))
 '(and (or q s) (or r s)))

(assert-acl2s-equal
 (dp-step 'p '(and (or p q) (or p r) (or s t)))
 '(or s t))

(assert-acl2s-equal
 (dp-step 'p '(and (or p q) (or (not p) (not q))))
 t)

(defun atom-formulas- (f)
  (match f
    ((type boolean) nil)
    ((type symbol) (list f))
    ((list* op args)
     (if (p-funp op)
         (reduce #'append (mapcar #'atom-formulas- args) :initial-value nil)
       (list f)))
    (_ nil)))

(defun atom-formulas (f)
  (remove-dups (atom-formulas- f)))

(defun empty-clause-p (c)
  (equal c nil))

(defun unsat-cnf-p (f)
  (some #'empty-clause-p (cnf-clauses f)))

(defun sat-cnf-p (f)
  (equal (zero-one-arity 'and (cnf-clauses f)) t))

(defun literal-var (lit)
  (match lit
    ((list 'not x) x)
    (_ lit)))

(defun choose-var (f)
  (car (remove-dups (mapcar #'literal-var (all-lits f)))))

(defun find-unit-literal (f)
  (let ((u (car (remove-if-not #'unit-clause-p (cnf-clauses f)))))
    (if u
        (car (clause-lits u))
      nil)))

(defun lit->assignment-pair (lit)
  (match lit
    ((list 'not x) (cons x nil))
    (_ (cons lit t))))

(defun extend-assignment (new old)
  (append new
          (remove-if #'(lambda (pr)
                         (assoc (car pr) new :test #'equal))
                     old)))

(defun lookup-asg (x asg)
  (let ((pr (assoc x asg :test #'equal)))
    (if pr (cdr pr) nil)))

(defun symbol-for-original-atom (a amap)
  (let ((pr (assoc a amap :test #'equal)))
    (if pr (cdr pr) a)))

(defun complete-assignment (atoms amap asg)
  (mapcar #'(lambda (a)
              (cons a (lookup-asg (symbol-for-original-atom a amap) asg)))
          atoms))

(defun add-unit-clause (lit f)
  (zero-one-arity 'and (cons lit (cnf-clauses f))))

(defun dp-cnf (f &optional (asg nil))
  (cond
    ((unsat-cnf-p f) 'unsat)
    ((sat-cnf-p f) (values 'sat asg))

    ;; unit propagation
    ((find-unit-literal f)
     (let* ((u (find-unit-literal f))
            (nf (one-literal-rule f))
            (na (extend-assignment (list (lit->assignment-pair u)) asg)))
       (dp-cnf nf na)))

    ;; pure literal elimination
    ((pure-literal f)
     (let* ((lit (pure-literal f))
            (nf (pure-literal-rule f))
            (na (extend-assignment (list (lit->assignment-pair lit)) asg)))
       (dp-cnf nf na)))

    ;; branch
    (t
     (let ((v (choose-var f)))
       (let+ (((&values s1 a1)
               (dp-cnf (add-unit-clause v f)
                       (extend-assignment (list (cons v t)) asg))))
         (if (equal s1 'sat)
             (values s1 a1)
           (dp-cnf (add-unit-clause `(not ,v) f)
                   (extend-assignment (list (cons v nil)) asg))))))))

(defun DP (f)
  (let* ((atoms (atom-formulas f))
         (sf (p-simplify f)))
    (cond
      ((equal sf nil) 'unsat)
      ((equal sf t) (values 'sat (mapcar #'(lambda (a) (cons a nil)) atoms)))
      (t
       (let+ (((&values sk amap) (p-skeleton sf))
              ((&values status asg)
               (dp-cnf (tseitin sk) nil)))
         (if (equal status 'unsat)
             'unsat
           (values 'sat (complete-assignment atoms amap asg))))))))

(time (DP '(and (or p q) (or (not p) r) (or (not q) r))))
(time (DP '(and (or p q)
                (or (not p) q)
                (or p (not q))
                (or (not p) (not q)))))
(time (DP '(and (or (foo x) q) (or (not (foo x)) r) (or p s) (or (not s) t))))


#|
 Part 2: DPLL
 Iterative version with explicit decision stack.
 Input is CNF, but arbitrary atoms are handled by p-skeleton first.
|#

(defun atom-formulas- (f)
  (match f
    ((type boolean) nil)
    ((type symbol) (list f))
    ((list* op args)
     (if (p-funp op)
         (reduce #'append (mapcar #'atom-formulas- args) :initial-value nil)
       (list f)))
    (_ nil)))

(defun atom-formulas (f)
  (remove-dups (atom-formulas- f)))

(defun literal-var (lit)
  (match lit
    ((list 'not x) x)
    (_ lit)))

(defun lit-truth (lit)
  (match lit
    ((list 'not x) nil)
    (_ t)))

(defun lit->assignment-pair (lit)
  (cons (literal-var lit) (lit-truth lit)))

(defun lookup-asg (x asg)
  (let ((pr (assoc x asg :test #'equal)))
    (if pr (cdr pr) nil)))

(defun extend-assignment (new old)
  (append new
          (remove-if #'(lambda (pr)
                         (assoc (car pr) new :test #'equal))
                     old)))

(defun complete-assignment (vars asg)
  (append asg
          (mapcar #'(lambda (v) (cons v nil))
                  (remove-if #'(lambda (v)
                                 (assoc v asg :test #'equal))
                             vars))))

(defun symbol-for-original-atom (a amap)
  (let ((pr (assoc a amap :test #'equal)))
    (if pr (cdr pr) a)))

(defun complete-original-assignment (atoms amap asg)
  (mapcar #'(lambda (a)
              (cons a (lookup-asg (symbol-for-original-atom a amap) asg)))
          atoms))

(defun empty-clause-p (c)
  (equal c nil))

(defun unsat-cnf-p (f)
  (some #'empty-clause-p (cnf-clauses f)))

(defun sat-cnf-p (f)
  (equal (zero-one-arity 'and (cnf-clauses f)) t))

(defun find-unit-literal (f)
  (let ((u (car (remove-if-not #'unit-clause-p (cnf-clauses f)))))
    (if u
        (car (clause-lits u))
      nil)))

(defun choose-var (f asg)
  (car (remove-if #'(lambda (v) (assoc v asg :test #'equal))
                  (remove-dups (mapcar #'literal-var (all-lits f))))))

(defun assign-cnf (lit f)
  ;; set lit=true:
  ;; - remove clauses containing lit
  ;; - remove (not lit) from remaining clauses
  (let* ((clauses (cnf-clauses f))
         (nlit (tseitin-neg lit))
         (kept (remove-if #'(lambda (c)
                              (in lit (clause-lits c)))
                          clauses))
         (shrunk (mapcar #'(lambda (c)
                             (zero-one-arity
                              'or
                              (remove nlit (clause-lits c) :test #'equal)))
                         kept)))
    (zero-one-arity 'and shrunk)))

(defun propagate-once (f asg)
  ;; returns 4 values:
  ;;   new-formula, new-assignment, changedp, conflictp
  (cond
    ((unsat-cnf-p f)
     (values f asg nil t))

    ((find-unit-literal f)
     (let* ((u (find-unit-literal f))
            (nf (assign-cnf u f))
            (na (extend-assignment (list (lit->assignment-pair u)) asg)))
       (values nf na t (unsat-cnf-p nf))))

    ((pure-literal f)
     (let* ((lit (pure-literal f))
            (nf (assign-cnf lit f))
            (na (extend-assignment (list (lit->assignment-pair lit)) asg)))
       (values nf na t (unsat-cnf-p nf))))

    (t
     (values f asg nil nil))))

(defun propagate-fixpoint (f asg)
  (let ((curf f)
        (cura asg))
    (loop
      do (let+ (((&values nf na changed conflict) (propagate-once curf cura)))
           (setf curf nf
                 cura na)
           (when conflict
             (return (values curf cura t)))
           (unless changed
             (return (values curf cura nil)))))))

(defun dpll-cnf (f)
  ;; iterative DPLL with explicit decision stack
  ;; stack entry = (saved-formula saved-assignment var tried-true)
  (let ((curf f)
        (asg nil)
        (stack nil))
    (loop
      do (let+ (((&values pf pa conflict) (propagate-fixpoint curf asg)))
           (setf curf pf
                 asg pa)

           (cond
             (conflict
              ;; backtrack to nearest decision whose false branch is untried
              (loop
                (when (endp stack)
                  (return-from dpll-cnf 'unsat))
                (let* ((frame (car stack))
                       (saved-f (first frame))
                       (saved-a (second frame))
                       (var     (third frame))
                       (tried-t (fourth frame)))
                  (setf stack (cdr stack))
                  (when tried-t
                    ;; now try var = nil
                    (setf curf (assign-cnf `(not ,var) saved-f)
                          asg  (extend-assignment (list (cons var nil)) saved-a))
                    (return)))))

             ((sat-cnf-p curf)
              (return-from dpll-cnf
                (values 'sat asg)))

             (t
              ;; decide a fresh variable, first try true
              (let ((v (choose-var curf asg)))
                (when (null v)
                  (return-from dpll-cnf
                    (values 'sat asg)))
                (push (list curf asg v t) stack)
                (setf curf (assign-cnf v curf)
                      asg  (extend-assignment (list (cons v t)) asg)))))))))

(defun DPLL (f)
  (let* ((atoms (atom-formulas f))
         (sf (p-simplify f)))
    (cond
      ((equal sf nil) 'unsat)
      ((equal sf t)
       (values 'sat (mapcar #'(lambda (a) (cons a nil)) atoms)))
      (t
       ;; input is promised CNF; p-skeleton handles non-prop atoms
       (let+ (((&values sk amap) (p-skeleton sf))
              ((&values status asg) (dpll-cnf sk)))
         (if (equal status 'unsat)
             'unsat
           (values 'sat
                   (complete-original-assignment atoms amap
                                                 (complete-assignment (pvars sk) asg)))))))))

;; --------------------------------------------------
;; evaluator-based test helpers
;; --------------------------------------------------

(defun xor-bool-list (xs)
  (oddp (count t xs :test #'equal)))

(defun eval-formula-under-asg (f asg)
  (match f
    ((type boolean) f)
    ((type symbol) (lookup-asg f asg))
    ((list* op args)
     (if (p-funp op)
         (match op
           ('and (every #'identity
                        (mapcar #'(lambda (x) (eval-formula-under-asg x asg)) args)))
           ('or  (some #'identity
                       (mapcar #'(lambda (x) (eval-formula-under-asg x asg)) args)))
           ('not (not (eval-formula-under-asg (car args) asg)))
           ('implies (or (not (eval-formula-under-asg (first args) asg))
                         (eval-formula-under-asg (second args) asg)))
           ('iff (or (endp args)
                     (endp (cdr args))
                     (every #'identity
                            (mapcar #'(lambda (pr)
                                        (equal (eval-formula-under-asg (first pr) asg)
                                               (eval-formula-under-asg (second pr) asg)))
                                    (mapcar #'list args (cdr args))))))
           ('xor (xor-bool-list
                  (mapcar #'(lambda (x) (eval-formula-under-asg x asg)) args)))
           ('if  (if (eval-formula-under-asg (first args) asg)
                     (eval-formula-under-asg (second args) asg)
                   (eval-formula-under-asg (third args) asg))))
       (lookup-asg f asg)))
    (_ nil)))

(defun assert-dpll-sat (f)
  (let+ (((&values status asg) (DPLL f)))
    (assert (equal status 'sat))
    (assert (eval-formula-under-asg f asg))))

(defun assert-dpll-unsat (f)
  (assert (equal (DPLL f) 'unsat)))

;; --------------------------------------------------
;; tests
;; --------------------------------------------------

(assert-dpll-unsat '(and p (not p)))
(assert-dpll-sat   '(or p (not p)))
(assert-dpll-sat   '(and p q))
(assert-dpll-sat   '(and p (or (not p) q)))
(assert-dpll-unsat '(and p (not p) q))
(assert-dpll-sat   '(and (or p q) (or (not p) r) (or (not q) r)))
(assert-dpll-unsat '(and (or p q)
                         (or (not p) q)
                         (or p (not q))
                         (or (not p) (not q))))
(assert-dpll-sat   '(and (or p q) (or r s)))
(assert-dpll-unsat '(and (or p q) (not q) (not p)))
(assert-dpll-sat   '(or (foo (if a b)) (not (foo (if a b)))))
(assert-dpll-sat   '(and (or (foo x) q) (or (not (foo x)) r)))
(assert-dpll-unsat '(and (foo x) (not (foo x))))

;; extra harder sat test
(assert-dpll-sat
 '(and
   (or p q r)
   (or (not p) s)
   (or (not q) s)
   (or (not r) t)
   (or (not s) u)
   (or (not t) u)
   (or (not u) v w)
   (or (not v) x)
   (or (not w) x)
   (or (not x) y)
   (or y z)
   (or (not z) p)))

;; simple profiling
(time (DPLL '(and (or p q) (or (not p) r) (or (not q) r))))
(time (DPLL '(and (or p q)
                  (or (not p) q)
                  (or p (not q))
                  (or (not p) (not q)))))
(time (DPLL '(and
              (or p q r)
              (or (not p) s)
              (or (not q) s)
              (or (not r) t)
              (or (not s) u)
              (or (not t) u)
              (or (not u) v w)
              (or (not v) x)
              (or (not w) x)
              (or (not x) y)
              (or y z)
              (or (not z) p))))

