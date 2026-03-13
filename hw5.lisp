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


#|
;; only list args should be sent here, others (symbol) in main loop
;; return reformulated args only
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

#|
(defun zero-one-arity (op args)
    (if (in op '(and or iff)) 
        (if (endp args)
            t
            (if (equal (len args) 1)
                (car args) 
                (cons op args)))
                (cons op args)))
|#
(assert (equal (zero-one-arity 'and '()) t))
(assert (equal (zero-one-arity 'or '()) nil))
(assert (equal (zero-one-arity 'iff '()) t))

(assert (equal (zero-one-arity 'and '(nil)) nil))
(assert (equal (zero-one-arity 'and '(p)) 'p))
(assert (equal (zero-one-arity 'and '(t)) t))

(assert (equal (zero-one-arity 'or '(nil)) nil))
(assert (equal (zero-one-arity 'or '(p)) 'p))
(assert (equal (zero-one-arity 'or '(t)) t))


(assert (equal (zero-one-arity 'iff '(nil)) nil))
(assert (equal (zero-one-arity 'iff '(p)) 'p))
(assert (equal (zero-one-arity 'iff '(t)) t))

;; return reformulated ops + args
(defun arbitrary-arity (op args)
    (if (in op '(and or iff xor)) 
      (cons op (mapcan #'(lambda (x) 
                  (match x
                    ((type boolean) (list x))
                    ((type symbol) (list x))
                    ((list* op2 args2)
                    (if (equal op2 op) args2 (list x)))
                  )
                ) args)) args))

(assert (equal (arbitrary-arity 'and '(p q (and r s))) '(and p q r s)))
(assert (equal (arbitrary-arity 'or '(p q (or r s))) '(or p q r s)))
(assert (equal (arbitrary-arity 'iff '(p q (iff r s))) '(iff p q r s)))
(assert (equal (arbitrary-arity 'xor '(p q (xor r s))) '(xor p q r s)))
(assert (equal (arbitrary-arity 'and '(p q (or r s))) '(and p q (or r s))))
(assert (equal (arbitrary-arity 'and '(p q (or r s) (and k y))) '(and p q (or r s) k
y)))


;; return t or nil or original op + args
(defun reduce-sink (op args)
  (match op
  ('and (if (in nil (remove-if-not #'booleanp args)) nil (cons op args)))
  ('or (if (in t (remove-if-not #'booleanp args)) t (cons op args)))
  (_ (cons op args))))

(assert (equal (reduce-sink 'and '(p q r s v nil)) nil))
(assert (equal (reduce-sink 'or '(p q r s v t)) t))
(assert (equal (reduce-sink 'iff '(p q r s v t))  '(iff p q r s v t)))
(assert (equal (reduce-sink 'and '(p q r s v nil)) nil))


;; and t x y => and x y
;; or nil x y => or x y
;; or nil => nil
(defun reduce-constants (op args)
  (match op
  ('and (cons op (remove t args)))
  ('or (if (equal args '(nil)) nil (cons op (remove nil args))))
  (_ (cons op args))))


(assert (equal (reduce-constants 'and '(t x y)) '(and x y)))
(assert (equal (reduce-constants 'or '(nil x y)) '(or x y)))
(assert (equal (reduce-constants 'or '(nil)) '(nil)))

(defun reduce-double (op args)
  (if (equal op 'not)
      (match (car args)
        ((list* 'not inner)
            (if (and (consp inner) (null (cdr inner)))
                (car inner)
                inner))
        ((list* 'iff rest) (cons 'xor rest))
        ((list* 'xor rest) (cons 'iff rest))
        (_ (cons op args)))
      (cons op args)))

(assert (equal (reduce-double 'not '((not z))) 'z))
(assert (equal (reduce-double 'not '((iff x y z))) '(xor x y z)))
(assert (equal (reduce-double 'not '((xor x y z))) '(iff x y z)))
(assert (equal (reduce-double 'not '((foo x y z))) '(not (foo x y z))))


(defun reduce-shannon (op args)
    (if (and (equal op 'and)
             (some #'atom args)
             (some #'consp args)
             (every #'(lambda (x) (or (atom x) (equal (car x) 'or))) args))
        (let* ((singletons (remove-if-not #'atom args))
                (or-args (mapcar #'cdr (remove-if #'atom args)))
                (common (if (endp or-args)
                            singletons
                            (reduce #'(lambda (a b) (intersection a b :test
                               #'equal))
                               or-args
                               :initial-value singletons))))
            (if (endp common)
                (cons op args)
                (car common)))
            (cons op args)))

(assert (equal (reduce-shannon 'and '((or p q) (or r q p) p)) 'p))
(assert (equal (reduce-shannon 'and '((or p q) (or r q p) q)) 'q))
(assert (equal (reduce-shannon 'and '((iff p q) (or r q p) p)) '(and (iff p q)
(or r q p) p)))
(assert (equal (reduce-shannon 'and '((or p q) (or r q p) r)) '(and (or p q) (or
r q p) r)))

(defun reduce-repetition (op args)
    (cons op (remove-dups args)))

(assert (equal (reduce-repetition 'and '(x y z x (or k y) (or k y) y x)) '(and z
(or k y) y x)))

(defun reduce-opposite (op args)
    (if (and (equal op 'or)
             (some #'(lambda (x) (in `(not ,x) args)) args))
        '(t)
        (cons op args)))

(assert (equal (reduce-opposite 'or '(x y (foo a b) z (not (foo a b)) w)) '(t)))



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
            (f3 (apply-reduction #'reduce-sink f2))
            (f4 (apply-reduction #'reduce-constants f3))
            (f5 (apply-reduction #'reduce-double f4))
            (f6 (apply-reduction #'reduce-repetition f5))
            (f7 (apply-reduction #'reduce-opposite f6))
            (f8 (apply-reduction #'reduce-shannon f7)))
       f8)))))

(defun p-simplify (f)
  (let ((result (p-simplify-once f)))
    (if (equal result f)
        result
        (p-simplify result))))

;; first flatten
;; then reduce sink
;; then remove constants for and and others 
;; then remove
#|
(defun p-simplify-once (f)
    (match f
    ((type boolean) f)
    ((type symbol) f)
    ((list* op args)
        (let* ((simplified-args (mapcar #'p-simplify-once args))
               (f1 (arbitrary-arity op simplified-args))
               (f2 (zero-one-arity (car f1) (cdr f1)))
               (op2 (if (consp f2) (car f2) nil)
               (args2 (if op2 (reduce-sink op2 args2) f2))
               (f3 (if op2 (reduce-sink op2 args2) f2))
               (op3 (if (consp f3) (car f3) nil))
               (args3 (if (consp f3) (cdr f3) nil))
               (f4 (if op3 (reduce-constants op3 args3) f3))
               (op4 (if (consp f4) (car f4) nil))
               (args4 (if (consp f4) (cdr f4) nil))
|#

;; A: constant removal
(assert-acl2s-equal (p-simplify '(and p t (foo t nil) q)) '(and p (foo t nil) q))
(assert-acl2s-equal (p-simplify '(and p t (foo t b) nil)) nil)
(assert-acl2s-equal (p-simplify '(or nil p q)) '(or p q))

;; B: flattening
(assert-acl2s-equal (p-simplify '(and p q (and r s) (or u v))) '(and p q r s (or u v)))
(assert-acl2s-equal (p-simplify '(and)) t)
(assert-acl2s-equal (p-simplify '(or p)) 'p)

;; C: sink elimination
(assert-acl2s-equal (p-simplify '(and p nil q)) nil)
(assert-acl2s-equal (p-simplify '(or p t q)) t)

;; D: double negation and not-iff/xor
(assert-acl2s-equal (p-simplify '(not (not p))) 'p)
(assert-acl2s-equal (p-simplify '(not (iff p q))) '(xor p q))
(assert-acl2s-equal (p-simplify '(not (xor p q))) '(iff p q))

;; E: shannon expansion
(assert-acl2s-equal (p-simplify '(and (or p q) (or r q p) p)) 'p)

;; F: duplicates and opposites
(assert-acl2s-equal (p-simplify '(or x y (foo a b) z (not (foo a b)) w)) t)
(assert-acl2s-equal (p-simplify '(and p q p r q)) '(and p q r))

;; deeply nested
(assert-acl2s-equal 
  (p-simplify '(and p (or nil x (and q q)) (not (not r)))) 
  '(and p (or x q) r))

;; all operators
(assert-acl2s-equal
  (p-simplify '(iff p (xor q (not (not q))) (and r t) (or s nil)))
  '(iff p (xor q q) r s))

|#






















