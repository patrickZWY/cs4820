#|

 Copyright © 2026 by Pete Manolios 
 CS 4820 Fall 2026

 Homework 5.
 Due: 3/12 (Midnight)

 For this assignment, work in groups of 1-2. Send me and the grader
 exactly one solution per team and make sure to follow the submission
 instructions on the course Web page. In particular, make sure that
 the subject of your email submission is "CS 4820 HWK 5".

 The group members are:

Christopher Wright-Williams
Wangyuan Zheng

 To make sure that we are all on the same page, build the latest
 version of ACL2s, as per HWK1. You are going to be using SBCL, which
 you already have, due to the build process in

 Next, install quicklisp. See https://www.quicklisp.org/beta/. 

 To make sure everything is OK with quicklisp and to initialize it,
 start sbcl and issue the following commands

 (load "~/quicklisp/setup.lisp")
 (ql:quickload :trivia)
 (ql:quickload :cl-ppcre)
 (ql:quickload :let-plus)
 (setf ppcre:*allow-named-registers* t)
 (exit) 

 Next, clone the ACL2s interface repository:
 (https) https://gitlab.com/acl2s/external-tool-support/interface.git
 (ssh)   git@gitlab.com:acl2s/external-tool-support/interface.git

 This repository includes scripts for interfacing with ACL2s from lisp.
 Put this directory in the ...books/acl2s/ of your ACL2 repository, or 
 use a symbolic link.

 Now, certify the books, by going to ...books/acl2s/interface and
 typing 

 "cert.pl -j 4 top"

 Look at the documentation for cert.pl. If cert.pl isn't in your path,
 then use

 "...books/build/cert.pl -j 4 top"

 The "-j 4" option indicates that you want to run up to 4 instances of
 ACL2 in parallel. Set this number to the number of cores you have.

 As mentioned at the beginning of the semester, some of the code we
 will write is in Lisp. You can find the common lisp manual online in
 various formats by searching for "common lisp manual."

 Other references that you might find useful and are available online
 include
 
 - Common Lisp: A Gentle Introduction to Symbolic Computation by David
   Touretzky
 - ANSI Common Lisp by Paul Graham
 
|#

(in-package "ACL2S")

;; Now for some ACL2s systems programming.

;; This book is already included in ACL2s, so this is a no-op, but I'm
;; putting it here so that you can see where the code for ACL2s
;; systems programming is coming from.
(include-book "acl2s/interface/top" :dir :system)
(set-ignore-ok t)

;; This gets us to raw lisp.
:q

#| 

 The interface books provide us with the ability to call the theorem
 prover within lisp, which will be useful in checking your code. 

 Here are some examples you can try. acl2s-compute is the form you use
 when you are using ACL2s to compute something, e.g., running a
 function on some input. acl2s-query is the form you use when you are
 querying ACL2s, e.g., a property without a name. If the property has
 a name, then that is not a query, but an event and you have to use
 acl2s-event.

 (acl2s-compute '(+ 1 2))
 (acl2s-query '(property (p q :all)
                 (iff (=> p q)
                      (v (! p) q))))
|#

#|

 Next, we need to load some software libraries using quicklisp.  For
 example, the trivia library provides pattern matching
 capabilities. Search for "match" below. Links to online documentation
 for the software libraries are provided below.

|#

(load "~/quicklisp/setup.lisp")

; See https://lispcookbook.github.io/cl-cookbook/pattern_matching.html
(ql:quickload :trivia)

; See https://www.quicklisp.org/beta/UNOFFICIAL/docs/cl-ppcre/doc/index.html
(ql:quickload :cl-ppcre)

; See https://github.com/sharplispers/let-plus
(ql:quickload :let-plus)

(setf ppcre:*allow-named-registers* t)

#|
 
 We now define our own package.

|#

(defpackage :tp (:use :cl :trivia :ppcre :let-plus :acl2 :acl2s))
(in-package :tp)

;; We import acl2s-compute and acl2s-query into our package.

(import 'acl2s-interface-internal::(acl2s-compute acl2s-query))

#|
 
 We have a list of the propositional operators and information about
 them. 

 :arity can be a positive integer or - (meaning arbitrary arity) If
 :arity is -, there must be an identity and the function must be
 associative and commutative.

 If :identity is non-nil, then the operator has the indicated
 identity. 
 
 An operator is idempotent iff :idem is t.

 If :sink is not -, then it must be the case that (op ... sink ...) =
 sink, e.g., (and ... nil ...) = nil.

 FYI: it is common for global variables to be enclosed in *'s. 

|# 

(defparameter *p-ops*
  '((and     :arity - :identity t   :idem t   :sink nil)
    (or      :arity - :identity nil :idem t   :sink t)
    (not     :arity 1 :identity -   :idem nil :sink -)
    (implies :arity 2 :identity -   :idem nil :sink -)
    (iff     :arity - :identity t   :idem nil :sink -)
    (xor     :arity - :identity nil :idem nil :sink -)
    (if      :arity 3 :identity -   :idem nil :sink -)))

#|

 mapcar is like map. See the common lisp manual.
 In general if you have questions about lisp, ask on Piazza.

|#

(defparameter *p-funs* (mapcar #'car *p-ops*))

#|

 See the definition of member in the common lisp manual.  Notice that
 there are different types of equality, including =, eql, eq, equal
 and equals. We need to be careful, so we'll just use equal and we'll
 define functions that are similar to the ACL2s functions we're
 familiar with.

|# 

(defun in (a x)
  (member a x :test #'equal))

(defmacro len (l) `(length ,l))

(defun p-funp (x)
  (in x *p-funs*))

;;assoc looks for an element in a list whose car matches the key
;; (key-alist->val 'iff *p-ops*) returns (iff :arity - :identity t :idem nil :sink -) AND (:arity - :identity t :idem nil :sink -)
(defun key-alist->val (k l)
  (let* ((in (assoc k l :test #'equal)))
    (values (cdr in) in)))

(key-alist->val 'iff *p-ops*)


(defun key-list->val (k l)
  (let* ((in (member k l :test #'equal)))
    (values (cadr in) in)))
;; returns - AND (:arity - :identity t :idem nil :sink -)
(key-list->val ':arity  (key-alist->val 'iff *p-ops*))

;Look up operator fun in *p-ops*, then inside that entry look up property key.
(defun pfun-key->val (fun key)
  (key-list->val key (key-alist->val fun *p-ops*)))

(defun remove-dups (l)
  (remove-duplicates l :test #'equal))

(defmacro == (x y) `(equal ,x ,y))
(defmacro != (x y) `(not (equal ,x ,y)))

(defparameter *booleans* '(t nil))

(defun booleanp (x)
  (in x *booleans*))

(defun pfun-argsp (pop args)
  (and (p-funp pop)
       (let ((arity (key-list->val :arity (key-alist->val pop *p-ops*))))
         (and (or (== arity '-)
                  (== (len args) arity))
              (every #'p-formulap args)))))

#|
 
 Here is the definition of a propositional formula. 
 
|#

(defun p-formulap (f)
  (match f
    ((type boolean) t) ; don't need this case, but here for emphasis
    ((type symbol) t)
    ((list* pop args)
     (if (p-funp pop)
         (pfun-argsp pop args)
       t))
    (_ nil)))

#|
 
 Notice that in addition to propositional variables, we allow atoms
 such as (foo x). 

 Here are some assertions (see the common lisp manual).
 
|#

(assert (p-formulap '(and)))
(assert (p-formulap '(and x y z)))
(assert (p-formulap '(and t nil)))
(assert (not (p-formulap '(implies x t nil))))
(assert (p-formulap 'q))
(assert (p-formulap '(implies (foo x) (bar y))))
(assert (p-formulap '(iff p q r s t)))
(assert (p-formulap '(xor p q r s t)))
(assert (not (p-formulap '(if p q r t))))

#|

 The propositional skeleton is what remains when we remove
 non-variable atoms.

|#

(defun p-skeleton-args (args amap acc)
  (if (endp args)
      (values (reverse acc) amap)
    (let+ (((&values na namap)
            (p-skeleton (car args) amap)))
          (p-skeleton-args (cdr args) namap (cons na acc)))))

(defun p-skeleton (f &optional amap) ;amap is nil if not specified
  (match f
    ((type symbol) (values f amap))
    ((list* pop args)
     (if (p-funp pop)
         (let+ (((&values nargs namap)
                 (p-skeleton-args args amap nil)))
               (values (cons pop nargs) namap))
       (let ((geta (key-alist->val f amap)))
         (if geta
             (values geta amap)
           (let ((gen (gentemp "P")))
             (values gen (acons f gen amap)))))))
    (_ (error "Not a p-formula"))))

#|

 Here are some examples you can try.

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

|#

#|

 Next we have some utilities for converting propositional formulas to
 ACL2s formulas.

|#

(defun nary-to-2ary (fun args)
  (let ((identity (pfun-key->val fun :identity)))
    (match args
      (nil identity)
      ((list x) (to-acl2s x))
      (_ (acl2s::xxxjoin (to-acl2s fun) (mapcar #'to-acl2s args))))))

(defun to-acl2s (f)
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

(defun acl2s-check-equal (f g)
  (let* ((iff `(iff ,f ,g))
         (siff (p-skeleton iff))
	 (pvars (pvars siff))
	 (aiff (to-acl2s siff))
         (af (second aiff))
         (ag (third aiff))
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

#|

; This will lead to an error. Try it.
; In sbcl :top gets you out of the debugger.
(assert-acl2s-equal 'p 'q)

|#

; Here is how we can use ACL2s to check our code.
(let* ((x '(or (foo a (g a c)) (g a c) (not (foo a (g a c))))))
  (assert-acl2s-equal x t))

(let* ((x '(or (foo a (g a c)) (g a c) (not (foo a (g a c)))))
       (sx (p-skeleton x)))
  (assert-acl2s-equal sx t))


#|
 
 Question 1. (25 pts)

 Define function, p-simplify that given a propositional formula
 returns an equivalent propositional formula with the following
 properties. 

 A. The skeleton of the returned formula is either a constant or does
 not include any constants. For example:

 (and p t (foo t nil) q) should be simplified to (and p (foo t nil) q)
 (and p t (foo t b) nil) should be simplified to nil

 B. Flatten expressions, e.g.:

 (and p q (and r s) (or u v)) is not flat, but this is
 (and p q r s (or u v))

 A formula of the form (op ...) where op is a Boolean operator of
 arbitrary arity (ie, and, or, iff) applied to 0 or 1 arguments is not
 flat. For example, replace (and) with t. 

 A formula of the form (op ... (op ...)) where op is a Boolean
 operator of arbitrary arity is not flat. For example, replace (and p
 q (and r s)) with (and p q r s).

 C. If there is Boolean constant s s.t. If (op ... s ...) = s, then we
 say that s is a sink of op. For example t is a sink of or. A formula
 is sink-free if no such subformulas remain. The returned formula
 should be sink-free.

 D. Simplify your formulas so that no subexpressions of the following
 form remain
 
 (not (not f))
 (not (iff ...))
 (not (xor ...))

 E. Apply Shannon expansions in 61-67.

 For example

 (and (or p q) (or r q p) p) should be simplified to

 p because (and (or t q) (or r q t) p) is (and t t p) is p

 F. Simplify formulas so that no subexpressions of the form

 (op ... p ... q ...)

 where p, q are equal literals or  p = (not q) or q = (not p).

 For example
 
 (or x y (foo a b) z (not (foo a b)) w) should be simplified to 

 t 

 Make sure that your algorithm is as efficient as you can make
 it. The idea is to use this simplification as a preprocessing step,
 so it needs to be fast. 

 You are not required to perform any other simplifications beyond
 those specified above. If you do, your simplifier must be guaranteed
 to always return something that is simpler that what would be
 returned if you just implemented the simplifications explicitly
 requested. Also, if you implement any other simplifications, your
 algorithm must run in comparable time (eg, no validity checking).
 Notice some simple consequences. You cannot transform the formula to
 an equivalent formula that uses a small subset of the
 connectives (such as not/and). If you do that, the formula you get
 can be exponentially larger than the input formula, as we have
 discussed in class. Notice that even negation normal form (NNF) can
 increase the size of a formula. Such considerations are important
 when you use Tseitin, because experience has shown that even
 transformations such as NNF are usually a bad idea when generating
 CNF, as they tend to result in CNF formulas that take modern solvers
 longer to analyze.

 Test your definition with assert-acl2s-equal using at least 10
 propositional formulas that include non-variable atoms, all of the
 operators, deeply nested formulas, etc.

 
|#

(defun flatten-op-args (op args)
  (if (== (pfun-key->val op :arity) '-)
      (reduce #'append
              (mapcar (lambda (a)
                        (if (and (consp a)
                                 (== (car a) op))
                            (copy-list (cdr a))
                            (list a)))
                      args)
              :initial-value nil)
      args))


(defun make-nary (op args)
  (cond
    ((and (== op 'and) (null args)) t)
    ((and (== op 'or)  (null args)) nil)
    ((and (== op 'iff) (null args)) t)
    ((and (== op 'xor) (null args)) nil)
    ((and (in op '(and or iff xor))
          (== (len args) 1))
     (first args))
    (t (cons op args))))

(defun negate-lit (x)
  (if (and (consp x) (== (car x) 'not))
      (cadr x)
      (list 'not x)))

(defun p-atomicp (x)
  (and (p-formulap x)
       (not (booleanp x))
       (not (and (consp x) (p-funp (car x))))))

(defun literalp (x)
  (or (p-atomicp x)
      (and (consp x)
           (== (car x) 'not)
           (p-atomicp (cadr x)))))

(defun lit-base (x)
  (if (and (consp x) (== (car x) 'not))
      (cadr x)
      x))

(defun lit-value (x)
  (not (and (consp x) (== (car x) 'not))))

(defun p-condition (f env)
  (match f
         ((type boolean) f)
         ((type symbol)
          (let ((hit (assoc f env :test #'equal)))
            (if hit (cdr hit) f)))
         ((list* pop args)
          (if (p-funp pop)
              (p-simplify (cons pop (mapcar (lambda (x) (p-condition x env)) args)))
              (let ((hit (assoc f env :test #'equal)))
                (if hit (cdr hit) f))))
         (_ f)))

(defun p-simplify (f)
  (match f
    ((type boolean) f)

    ((type symbol) f)

    ((list* op args)
     (if (not (p-funp op))
         f
       (let* ((sargs (mapcar #'p-simplify args))
              (sargs (flatten-op-args op sargs)))
         (case op
           (not
            (let ((a (first sargs)))
              (cond
                ((and (consp a) (== (car a) 'not))  (p-simplify (cadr a)))  ; re-simplify
                ((and (consp a) (== (car a) 'iff))  (p-simplify (cons 'xor (cdr a))))  ; re-simplify
                ((and (consp a) (== (car a) 'xor))  (p-simplify (cons 'iff (cdr a))))  ; re-simplify
                ((booleanp a)                        (not a))                         ; (not t)=nil, (not nil)=t
                (t                                   (list 'not a)))))

           (and
            (let* ((lits   (remove-if-not #'literalp sargs))
                   (others (remove-if #'literalp sargs))
                   (env    (mapcar (lambda (lit)
                                     (cons (lit-base lit) (lit-value lit)))
                                   lits))
                   (others (mapcar (lambda (x) (p-condition x env)) others))
                   (sargs  (append lits others))
                   (sargs  (flatten-op-args 'and sargs)))

              (when (member nil sargs :test #'equal)
                (return-from p-simplify nil))

              (setf sargs (remove t sargs :test #'equal))

              (when (some (lambda (x)
                            (member (negate-lit x) sargs :test #'equal))
                          sargs)
                (return-from p-simplify nil))

              (make-nary 'and (remove-dups sargs))))

           (or
            (let* ((lits   (remove-if-not #'literalp sargs))
                   (others (remove-if #'literalp sargs))
                   (env    (mapcar (lambda (lit) 
                                     (cons (lit-base lit) (not (lit-value lit))))
                                   lits))               ; the arg to mapcar
                   (others (mapcar (lambda (x) (p-condition x env)) others))
                   (sargs  (append lits others))
                   (sargs  (flatten-op-args 'or sargs)))

              (when (member t sargs :test #'equal)
                (return-from p-simplify t))

              (setf sargs (remove nil sargs :test #'equal))

              (when (some (lambda (x)
                            (member (negate-lit x) sargs :test #'equal))
                          sargs)
                (return-from p-simplify t))

              (make-nary 'or (remove-dups sargs))))

           (implies
            (destructuring-bind (p q) sargs
              (cond ((== p nil) t)
                    ((== p t)   q)
                    ((== q t)   t)
                    ((== q nil) (p-simplify `(not ,p)))
                    ((== p q)   t)
                    (t          `(implies ,p ,q)))))

           (if
            (destructuring-bind (c tb fb) sargs
              (cond ((== c t)    tb)
                    ((== c nil)  fb)
                    ((== tb fb)  tb)
                    ((== tb t)   (p-simplify `(or ,c ,fb)))
                    ((== tb nil) (p-simplify `(and (not ,c) ,fb)))
                    ((== fb t)   (p-simplify `(or (not ,c) ,tb)))
                    ((== fb nil) (p-simplify `(and ,c ,tb)))
                    (t           `(if ,c ,tb ,fb)))))

           ;; For iff: identity is t (remove), nil flips polarity (count them)
           (iff
            (let* ((nil-count (count nil sargs :test #'equal))
                   (sargs     (remove nil sargs :test #'equal))
                   (sargs     (remove t   sargs :test #'equal))
                   (has-comp  (some (lambda (x)
                                      (member (negate-lit x) sargs :test #'equal))
                                    sargs))
                   (base      (if has-comp
                                  nil
                                  (make-nary 'iff (remove-dups sargs)))))
              (if (oddp nil-count)
                  (p-simplify `(not ,base))
                  base)))

           ;; For xor: identity is nil (remove), t flips polarity (count them)
           (xor
            (let* ((t-count  (count t   sargs :test #'equal))
                   (sargs    (remove t   sargs :test #'equal))
                   (sargs    (remove nil sargs :test #'equal))
                   (has-comp (some (lambda (x)
                                     (member (negate-lit x) sargs :test #'equal))
                                   sargs))
                   (base     (if has-comp
                                 t
                                 (make-nary 'xor (remove-dups sargs)))))
              (if (oddp t-count)
                  (p-simplify `(not ,base))
                  base)))

           (otherwise (cons op sargs))))))

    (_ f)))

(assert-acl2s-equal (p-simplify '(and p t q)) '(and p q))
(assert-acl2s-equal (p-simplify '(and p nil q)) nil)
(assert-acl2s-equal (p-simplify '(or p nil q)) '(or p q))
(assert-acl2s-equal (p-simplify '(or p t q)) t)

;;  Flattening
(assert-acl2s-equal (p-simplify '(and p q (and r s))) '(and p q r s))
(assert-acl2s-equal (p-simplify '(or p q (or r s))) '(or p q r s))
(assert-acl2s-equal (p-simplify '(and p)) 'p)
(assert-acl2s-equal (p-simplify '(and)) t)
(assert-acl2s-equal (p-simplify '(or)) nil)

;; C: Sink propagation
(assert-acl2s-equal (p-simplify '(and p nil q)) nil)
(assert-acl2s-equal (p-simplify '(or p t q)) t)

(assert-acl2s-equal (p-simplify '(not (not p))) 'p)

;; E: Shannon expansion
(assert-acl2s-equal (p-simplify '(and (or p q) (or r q p) p)) 'p)

;; implies cases
(assert-acl2s-equal (p-simplify '(implies nil q)) t)
(assert-acl2s-equal (p-simplify '(implies t q)) 'q)
(assert-acl2s-equal (p-simplify '(implies p t)) t)

;; if cases
(assert-acl2s-equal (p-simplify '(if t p q)) 'p)
(assert-acl2s-equal (p-simplify '(if nil p q)) 'q)

;; non-variable atoms
(assert-acl2s-equal (p-simplify '(and (foo x) t (bar y))) '(and (foo x) (bar y)))
(assert-acl2s-equal (p-simplify '(or (foo x) nil (bar y))) '(or (foo x) (bar y)))

#|

 Question 2. (20 pts)

 Define tseitin, a function that given a propositional formula,
 something that satisfies p-formulap, applies the tseitin
 transformation to generate a CNF formula that is equi-satisfiable.

 Remember that you have to deal with atoms such as

 (foo (if a b))

 You should simplify the formula first, using p-simplify, but do not
 perform any other simplifications. Any simpification you want to
 perform must be done in p-simplify.

 Test tseitin using with assert-acl2s-equal using at least 10
 propositional formulas.

|#

;; Process args recursively, collecting reps and clauses
(defun tseitin-args (args)
  (if (endp args)
      (values nil nil)
    (multiple-value-bind (rep clauses) (tseitin-rec (car args))
      (multiple-value-bind (rest-reps rest-clauses) (tseitin-args (cdr args))
        (values (cons rep rest-reps)
                (append clauses rest-clauses))))))

;; Generate clauses encoding z <-> (op zs)
(defun tseitin-clauses (op z zs)
  (let ((nz `(not ,z)))
    (case op
      ;; z <-> (not a)
      (not
       (let ((a (first zs)))
         (list `(or ,z ,a)
               `(or ,nz (not ,a)))))
      ;; z <-> (and z1 ... zn)
      (and
       (cons `(or ,z ,@(mapcar (lambda (zi) `(not ,zi)) zs))
             (mapcar (lambda (zi) `(or ,nz ,zi)) zs)))
      ;; z <-> (or z1 ... zn)
      (or
       (cons `(or ,nz ,@zs)
             (mapcar (lambda (zi) `(or ,z (not ,zi))) zs)))
      ;; z <-> (implies a b) treated as z <-> (or (not a) b)
      (implies
       (let ((a (first zs)) (b (second zs)))
         (list `(or ,nz (not ,a) ,b)
               `(or ,z ,a)
               `(or ,z (not ,b)))))
      ;; z <-> (iff a b)
      (iff
       (let ((a (first zs)) (b (second zs)))
         (list `(or ,nz (not ,a) ,b)
               `(or ,nz ,a (not ,b))
               `(or ,z ,a ,b)
               `(or ,z (not ,a) (not ,b)))))
      ;; z <-> (xor a b)
      (xor
       (let ((a (first zs)) (b (second zs)))
         (list `(or ,nz (not ,a) (not ,b))
               `(or ,nz ,a ,b)
               `(or ,z (not ,a) ,b)
               `(or ,z ,a (not ,b)))))
      ;; z <-> (if c a b)
      (if
       (let ((c (first zs)) (a (second zs)) (b (third zs)))
         (list `(or ,nz (not ,c) ,a)
               `(or ,nz ,c ,b)
               `(or ,z (not ,c) (not ,a))
               `(or ,z ,c (not ,b))))))))

(defun tseitin-rec (f)
  (cond
    ;; Boolean constants
    ((booleanp f) (values f nil))
    ;; Atoms (variables, non-prop compound atoms like (foo x))
    ((not (and (consp f) (p-funp (car f)))) (values f nil))
    ;; Compound propositional formula
    (t
     (let ((op (car f))
           (args (cdr f)))
       ;; Reduce multi-arg iff/xor to binary (left-associative)
       (when (and (in op '(iff xor)) (> (len args) 2))
         (return-from tseitin-rec
           (tseitin-rec `(,op ,(car args) (,op ,@(cdr args))))))
       (multiple-value-bind (zs sub-clauses) (tseitin-args args)
         (let* ((z (gentemp "Z"))
                (own-clauses (tseitin-clauses op z zs)))
           (values z (append sub-clauses own-clauses))))))))

(defun tseitin (f)
  (let ((sf (p-simplify f)))
    (cond
      ((== sf t)   t)
      ((== sf nil) '(and (or)))  ; empty clause = unsat
      (t
       (multiple-value-bind (z clauses) (tseitin-rec sf)
         ;; Assert the top-level variable is true
         (cons 'and (cons `(or ,z) clauses)))))))


;; ******************** Used LLM to get these test cases ***************************************
;; Helper: check the tseitin output is in CNF form (and of ors)
(defun cnfp (f)
  (and (consp f)
       (== (car f) 'and)
       (every (lambda (clause)
                (and (consp clause)
                     (== (car clause) 'or)))
              (cdr f))))

;; 1. Simple and -- should produce CNF with z <-> (and p q)
(let ((result (tseitin '(and p q))))
  (format t "~%and: ~a~%" result)
  (assert (cnfp result)))

;; 2. Simple or
(let ((result (tseitin '(or p q))))
  (format t "~%or: ~a~%" result)
  (assert (cnfp result)))

;; 3. Tautology -- p or not p, tseitin result should be satisfiable
(let ((result (tseitin '(or p (not p)))))
  (format t "~%tautology: ~a~%" result)
  (assert (== result t)))  ; p-simplify catches this before tseitin runs

;; 4. Contradiction -- tseitin result should be unsatisfiable
(let ((result (tseitin '(and p (not p)))))
  (format t "~%contradiction: ~a~%" result)
  (assert (== result '(and (or)))))  ; p-simplify catches this too

;; 5. implies
(let ((result (tseitin '(implies p q))))
  (format t "~%implies: ~a~%" result)
  (assert (cnfp result)))

;; 6. nested formula from slides: (and (or p (and q (not r))) s)
(let ((result (tseitin '(and (or p (and q (not r))) s))))
  (format t "~%nested: ~a~%" result)
  (assert (cnfp result)))

;; 7. iff 
(let ((result (tseitin '(iff p q))))
  (format t "~%iff: ~a~%" result)
  (assert (cnfp result)))

;; 8. xor
(let ((result (tseitin '(xor p q))))
  (format t "~%xor: ~a~%" result)
  (assert (cnfp result)))

;; 9. non-variable atom -- (foo x) should be treated as an atom
(let ((result (tseitin '(and (foo x) (bar y)))))
  (format t "~%atoms: ~a~%" result)
  (assert (cnfp result)))

;; 10. if
(let ((result (tseitin '(if p q r))))
  (format t "~%if: ~a~%" result)
  (assert (cnfp result)))

;; 11. deeply nested
(let ((result (tseitin '(and (or p (iff q r)) (implies s (xor p q))))))
  (format t "~%deep: ~a~%" result)
  (assert (cnfp result)))

#|

 Question 3. (30 pts)

 Define DP, a function that given a propositional formula in CNF,
 applies the Davis-Putnam algorithm to determine if the formula is
 satisfiable.

 Remember that you have to deal with atoms such as

 (foo (if a b))

 If the formula is sat, DP returns 'sat and a satisfying assignment: an
 alist mapping each atom in the formula to t/nil. Use values to return
 multiple values.

 If it is usat, return 'unsat.

 Do some profiling

 Test DP using with assert-acl2s-equal using at least 10
 propositional formulas. 

 It is easy to extend dp to support arbitrary formulas by using
 tseitin to generate CNF.

|#

;;                                               --- CNF helpers ---

;; converts a CNF formula into a list of clauses.
(defun cnf->clauses (f)
  (cond ((== f t)   nil) ;; empty conjunction.
        ((== f nil) '((or))) ;; empty disjunction
        ((and (consp f) (== (car f) 'and)) (cdr f)) ; If the formula is already an explicit conjunction of clauses, return the clauses
        (t (list f)))) ; if the formula is not an 'and, then treat it as a single clause formula


;; It converts one clause into its list of literals.
(defun clause->lits (c)
  (cond ((and (consp c) (== (car c) 'or)) (cdr c))
        (t (list c))))

;; Note: lit->atom handles compound atoms like (foo x) since they won't
;; match (not ...)
;; It strips off negation and returns the underlying atom of a literal.
(defun lit->atom (l)
  (if (and (consp l) (== (car l) 'not))
      (cadr l)
      l))

; tells you whether a literal is positive.
(defun lit-pos? (l)
  (not (and (consp l) (== (car l) 'not))))

;; gets all variables/atoms occurring in the CNF
(defun clauses->atoms (clauses)
  (remove-dups
   (mapcar #'lit->atom
           (apply #'append (mapcar #'clause->lits clauses)))))


;;                                          --- Literal propagation ---

;; Remove satisfied clauses, strip the negation of lit from others
(defun propagate-lit (lit clauses)
  (let ((neg (negate-lit lit)))
    (loop for c in clauses
          for lits = (clause->lits c)
          unless (member lit lits :test #'equal)
            collect (cons 'or (remove neg lits :test #'equal)))))

;;                                             --- BCP to fixpoint ---

(defun bcp (clauses assign)
  (let ((unit (find-if (lambda (c) (== (length (clause->lits c)) 1)) clauses)))
    (if (null unit)
        (values clauses assign)
        (let* ((lit  (first (clause->lits unit)))
               (atom (lit->atom lit))
               (val  (lit-pos? lit)))
          (bcp (propagate-lit lit clauses)
               (acons atom val assign))))))

;;                                    --- Pure literal rule to fixpoint ---

(defun pure-literals (clauses)
  (let ((all-lits (remove-dups (apply #'append (mapcar #'clause->lits clauses)))))
    (remove-if (lambda (l) (member (negate-lit l) all-lits :test #'equal))
               all-lits)))

(defun apply-pure-lits (clauses assign)
  (let ((pures (pure-literals clauses)))
    (if (null pures)
        (values clauses assign)
        (let* ((new-assign
                 (reduce (lambda (a l) (acons (lit->atom l) (lit-pos? l) a))
                         pures :initial-value assign))
               (new-clauses
                 (reduce (lambda (cs l) (propagate-lit l cs))
                         pures :initial-value clauses)))
          (apply-pure-lits new-clauses new-assign)))))


;;                                --- Preprocessing: BCP + pure lits to fixpoint ---

(defun preprocess (clauses assign)
  (multiple-value-bind (c1 a1) (bcp clauses assign)
    (multiple-value-bind (c2 a2) (apply-pure-lits c1 a1)
      ;; Fixpoint check using sizes (cheaper than full equal comparison)
      (if (and (== (length c2) (length clauses))
               (== (length a2) (length assign)))
          (values c2 a2)
          (preprocess c2 a2)))))

;;                                         --- Resolution on variable x ---

(defun has-lit? (clause lit)
  (member lit (clause->lits clause) :test #'equal))

;; Returns (values new-clauses pos-clauses neg-clauses)
;; so we can reconstruct x's value later
(defun resolve-on-var (x clauses)
  (let* ((pos    (remove-if-not (lambda (c) (has-lit? c x)) clauses))
         (neg    (remove-if-not (lambda (c) (has-lit? c `(not ,x))) clauses))
         (other  (remove-if (lambda (c) (or (has-lit? c x)
                                            (has-lit? c `(not ,x))))
                            clauses))
         (resolvents                    ; <-- needs the wrapping ( before it
           (loop for pc in pos
                 append
                 (loop for nc in neg
                       for res-lits = (remove-dups
                                       (append
                                        (remove x (clause->lits pc) :test #'equal)
                                        (remove `(not ,x) (clause->lits nc) :test #'equal)))
                       unless (some (lambda (l)
                                      (member (negate-lit l) res-lits :test #'equal))
                                    res-lits)
                         collect (cons 'or res-lits)))))
    (values (append other resolvents) pos neg)))

;;                            --- Assignment reconstruction for eliminated variable x ---

(defun clause-sat-under? (clause assign)
  (some (lambda (lit)
          (let* ((atom    (lit->atom lit))
                 (pos     (lit-pos? lit))
                 (binding (assoc atom assign :test #'equal)))
            (and binding (== (cdr binding) pos))))
        (clause->lits clause)))



;; After resolution on x, given the satisfying assign for remaining vars:
;; If all neg-clauses (those with (not x)) are already satisfied → x=t works
;; Otherwise some neg-clause needs (not x) to be true → x=nil
;; (In the latter case, pos-clauses must already be satisfied by the resolvents argument)
(defun reconstruct-x-val (pos-clauses neg-clauses assign)
  (let ((need-true  (some (lambda (c) (not (clause-sat-under? c assign))) pos-clauses))
        (need-false (some (lambda (c) (not (clause-sat-under? c assign))) neg-clauses)))
    (cond
      ((and need-true  (not need-false)) t)
      ((and need-false (not need-true))  nil)
      ;; Both unsatisfied = tautological resolvent was discarded,
      ;; either value could work — default t (consistent with fill-with-t below)
      (t t))))

;;                                             --- Empty clause check ---

(defun has-empty-clause? (clauses)
  (some (lambda (c) (null (clause->lits c))) clauses))


;;                                         --- Main DP recursive core ---

(defun dp-clauses (clauses assign)
  ;; Base: empty clause → UNSAT
  (when (has-empty-clause? clauses)
    (return-from dp-clauses (values 'unsat nil)))
  ;; Base: no clauses → SAT
  (when (null clauses)
    (return-from dp-clauses (values 'sat assign)))

  ;; Preprocess
  (multiple-value-bind (clauses1 assign1) (preprocess clauses assign)
    ;; Recheck bases after preprocessing
    (when (has-empty-clause? clauses1)
      (return-from dp-clauses (values 'unsat nil)))
    (when (null clauses1)
      (return-from dp-clauses (values 'sat assign1)))

    ;; Choose first available atom and eliminate via resolution
    (let ((x (first (clauses->atoms clauses1))))
      (multiple-value-bind (new-clauses pos-clauses neg-clauses)
          (resolve-on-var x clauses1)
        (multiple-value-bind (result assign2) (dp-clauses new-clauses assign1)
          (if (== result 'unsat)
              (values 'unsat nil)
              ;; SAT: reconstruct x's value and add to assignment
              (let* ((x-val      (reconstruct-x-val pos-clauses neg-clauses assign2))
                     (full-assign (acons x x-val assign2)))
                (values 'sat full-assign))))))))


;;                                             --- Top-level dp ---

(defun dp (f)
  (cond
    ((== f t)   (values 'sat nil))
    ((== f nil) (values 'unsat nil))
    (t
     (let* ((clauses    (cnf->clauses f))
            (all-atoms  (clauses->atoms clauses)))
       (multiple-value-bind (result assign) (dp-clauses clauses nil)
         (if (== result 'unsat)
             (values 'unsat nil)
             ;; Fill in any atoms that BCP/pure-lits didn't touch (assign t arbitrarily)
             (let ((full-assign
                     (reduce (lambda (a atom)
                               (if (assoc atom a :test #'equal) a (acons atom t a)))
                             all-atoms :initial-value assign)))
               (values 'sat full-assign))))))))

;; --- Verification helper for testing ---

(defun verify-sat (f assign)
  "Check that assign actually satisfies f (as a CNF clause set)"
  (every (lambda (c) (clause-sat-under? c assign))
         (cnf->clauses f)))

;; --- Tests ---

;; Helper: run dp and assert result matches expected sat/unsat
(defun assert-dp (f expected-result)
  (multiple-value-bind (result assign) (dp f)
    (assert (== result expected-result))
    (when (== result 'sat)
      (assert (verify-sat f assign)))
    result))

;; 1. Simple satisfiable: (and (or p q))
(assert-dp '(and (or p q)) 'sat)

;; 2. Unsatisfiable: p and not-p
(assert-dp '(and (or p) (or (not p))) 'unsat)

;; 3. Tautology via tseitin: (or p (not p)) → simplifies to t
(assert (== (dp t) (values 'sat nil)))

;; 4. Contradiction: (and (or)) - empty clause
(assert-dp '(and (or)) 'unsat)

;; 5. Pure literal: p only appears positively
(assert-dp '(and (or p q) (or p r)) 'sat)

;; 6. Unit propagation chain: p forced, then p->q forced
(assert-dp '(and (or p) (or (not p) q) (or (not q) r)) 'sat)

;; 7. Larger UNSAT instance (Horn-like contradiction)
(assert-dp '(and (or p) (or q) (or (not p) (not q))) 'unsat)

;; 8. Formula with compound (non-variable) atoms
(assert-dp '(and (or (foo x) (bar y)) (or (not (foo x)) (baz z))) 'sat)

;; 9. Multiple clauses, needs resolution to settle
(assert-dp '(and (or p q) (or (not p) r) (or (not q) r) (or (not r))) 'unsat)

;; 10. Satisfiable with 4 vars
(assert-dp '(and (or p q) (or (not p) r) (or (not r) s) (or (not s) q)) 'sat)

;; 11. Test that assignment actually satisfies the formula (3-var instance)
(multiple-value-bind (result assign)
    (dp '(and (or p (not q)) (or (not p) r) (or q (not r))))
  (assert (== result 'sat))
  (assert (verify-sat '(and (or p (not q)) (or (not p) r) (or q (not r))) assign)))

;; 12. tseitin roundtrip test: formula, tseitin, dp
(let* ((f   '(and (or p q) (or r s)))
       (cnf (tseitin f))
       (res (dp cnf)))
  (assert (== res 'sat)))


#|

 Question 4.

 Part1: (25pts) Profile DP and make it as efficient as possible. If it
 meets the efficiency criteria of the evaluator, you get credit. The
 fastest submission will get 20 extra points, no matter how slow. To
 generate interesting problems, see your book.

 Part 2: (30pts) Define DPLL, a function that given a propositional
 formula in CNF, applies the DPLL algorithm to determine if the
 formula is satisfiable. You have to implement the iterative with
 backjumping version of DPLL from the book.

 Remember that you have to deal with atoms such as

 (foo (if a b))

 If the formula is sat, DPLL returns 'sat and a satisfying assignment:
 an alist mapping each atom in the formula to t/nil. Use values to
 return multiple values.

 If it is usat, return 'unsat.

 Test DPLL using with assert-acl2s-equal using at least 10
 propositional formulas.

 The fastest submission will get 20 extra points, no matter how
 slow. To generate interesting problems, see your book.

|#



;; Algorithm (from L10 slides):
;;   Trail: list of (atom val level reason), newest-first
;;     reason=nil → decision; reason=clause → BCP implication
;;   Loop:
;;     1. BCP to fixpoint
;;     2. If conflict:
;;          if level=0 → UNSAT
;;          else → analyze conflict → asserting clause (1-UIP)
;;                 backjump to assertion level (2nd-highest in clause)
;;                 add learned clause; BCP immediately asserts UIP literal
;;     3. If no conflict:
;;          if all assigned → SAT
;;          else → pick unassigned var, make decision, bump level

;; --- Trail entry accessors (atom val level reason) ---

(defun mk-te (a v l r) (list a v l r))
(defun te-a (e) (car    e))   ; atom
(defun te-v (e) (cadr   e))   ; value (t/nil)
(defun te-l (e) (caddr  e))   ; decision level
(defun te-r (e) (cadddr e))   ; reason clause (nil = free decision)

(defun trail-entry (atom trail)
  "Find trail entry for atom, or nil (trail is newest-first)"
  (find atom trail :key #'te-a :test #'equal))

(defun trail-val (atom trail)
  "Return (values val found)"
  (let ((e (trail-entry atom trail)))
    (if e (values (te-v e) t) (values nil nil))))

;; --- Literal evaluation under trail ---

(defun dpll-lit-val (lit trail)
  "Return (values bool assigned?)"
  (multiple-value-bind (v found) (trail-val (lit->atom lit) trail)
    (if found
        (values (if (lit-pos? lit) v (not v)) t)
        (values nil nil))))

;; --- Clause status ---
;; Returns :sat | :unsat | (:unit asserting-lit) | :unresolved

(defun dpll-clause-status (clause trail)
  (let ((unassigned '()))
    (dolist (lit (clause->lits clause))
      (multiple-value-bind (v found) (dpll-lit-val lit trail)
        (cond
          ((and found v) (return-from dpll-clause-status :sat))
          ((not found)   (push lit unassigned)))))
    (cond
      ((null unassigned)       :unsat)
      ((null (cdr unassigned)) (values :unit (car unassigned)))
      (t                       :unresolved))))

;; --- BCP to fixpoint ---
;; Returns (values trail conflict-clause-or-nil)

(defun dpll-bcp (clauses trail level)
  (let ((changed t))
    (loop while changed
          do (setf changed nil)
             (dolist (cl clauses)
               (multiple-value-bind (status unit-lit) (dpll-clause-status cl trail)
                 (case status
                   (:unsat (return-from dpll-bcp (values trail cl)))
                   (:unit
                    (let ((a (lit->atom unit-lit)))
                      (unless (trail-entry a trail)
                        (push (mk-te a (lit-pos? unit-lit) level cl) trail)
                        (setf changed t))))))))
    (values trail nil)))

;; --- 1-UIP Conflict Analysis ---
;;
;; Input:  conflict-clause (falsified), trail, current level
;; Output: (values learned-clause backjump-level asserting-lit)
;;
;; Strategy: resolve the conflict clause against reason clauses of
;; the most-recently-assigned implied literals at the current level,
;; until exactly 1 current-level literal remains (1-UIP).
;; The learned clause is asserting: 1 lit at conflict level, rest ≤ bj-level.
;; Backjump level = 2nd-highest level in learned clause (or -1 if only one level).

(defun dpll-analyze (conflict-clause trail level)
  (let ((work (copy-list (clause->lits conflict-clause))))
    (loop
      ;; Collect current-level lits and those with reasons (BCP-implied)
      (let* ((curr-lits
               (remove-if-not
                (lambda (l)
                  (let ((e (trail-entry (lit->atom l) trail)))
                    (and e (= (te-l e) level))))
                work))
             (implied
               (remove-if-not
                (lambda (l)
                  (let ((e (trail-entry (lit->atom l) trail)))
                    (and e (= (te-l e) level) (te-r e))))
                curr-lits)))
        ;; Stop when ≤1 current-level lit (1-UIP found) or nothing to resolve
        (when (or (<= (length curr-lits) 1) (null implied))
          (return))
        ;; Pick most-recently-assigned implied lit (smallest index = newest in trail)
        (let* ((resolve-lit
                 (reduce
                  (lambda (best l)
                    (if (< (or (position (lit->atom l)    trail :key #'te-a :test #'equal) 999999)
                           (or (position (lit->atom best) trail :key #'te-a :test #'equal) 999999))
                        l best))
                  (cdr implied)
                  :initial-value (car implied)))
               (a       (lit->atom resolve-lit))
               (r-lits  (clause->lits (te-r (trail-entry a trail)))))
          ;; Resolve: remove atom 'a' from both sides, merge
          (setf work
                (remove-dups
                 (append
                  (remove-if (lambda (l) (equal (lit->atom l) a)) work)
                  (remove-if (lambda (l) (equal (lit->atom l) a)) r-lits)))))))
    ;; Extract UIP literal (the one remaining at conflict level)
    (let* ((uip (find-if
                 (lambda (l)
                   (let ((e (trail-entry (lit->atom l) trail)))
                     (and e (= (te-l e) level))))
                 work))
           ;; Backjump level = max level strictly below conflict level
           ;; (= "2nd-highest level in learned clause", or -1 if no such lit)
           (bj (reduce
                (lambda (acc l)
                  (let ((e (trail-entry (lit->atom l) trail)))
                    (if (and e (< (te-l e) level))
                        (max acc (te-l e))
                        acc)))
                work
                :initial-value -1)))
      (values (cons 'or work) bj uip))))

;; --- Backjump: remove all trail entries above bj-level ---

(defun dpll-bj (trail bj-level)
  (remove-if (lambda (e) (> (te-l e) bj-level)) trail))

;; --- Variable selection: first unassigned atom ---

(defun dpll-pick (all-atoms trail)
  (find-if (lambda (a) (not (trail-entry a trail))) all-atoms))

;; --- Main iterative DPLL loop ---

(defun dpll-loop (init-clauses all-atoms)
  (let ((clauses (copy-list init-clauses))   ; grows with learned clauses
        (trail   '())
        (level    0))
    (loop
      ;; Step 1: BCP
      (multiple-value-bind (new-trail conflict)
          (dpll-bcp clauses trail level)
        (setf trail new-trail)
        (cond
          ;; --- Conflict ---
          (conflict
           (cond
             ;; UNSAT: conflict at level 0, no decisions to undo
             ((= level 0)
              (return (values 'unsat nil)))
             (t
              (multiple-value-bind (learned bj uip)
                  (dpll-analyze conflict trail level)
                (cond
                  ;; Safety fallback: if analysis fails to find UIP,
                  ;; do chronological backtrack (shouldn't happen in correct CNF)
                  ((null uip)
                   (setf trail (dpll-bj trail (1- level)))
                   (setf level (1- level)))
                  (t
                   ;; Add learned clause, backjump, assert UIP literal
                   (push learned clauses)
                   (setf trail (dpll-bj trail (max bj 0)))
                   (setf level (max bj 0))
                   ;; Assert: make the UIP literal true
                   ;;   lit-pos? gives the polarity we need for atom
                   (push (mk-te (lit->atom uip) (lit-pos? uip) level learned)
                         trail)))))))
          ;; --- No conflict ---
          (t
           (let ((next (dpll-pick all-atoms trail)))
             (cond
               ;; All atoms assigned → SAT
               ((null next)
                (return (values 'sat
                                (mapcar (lambda (e) (cons (te-a e) (te-v e)))
                                        trail))))
               ;; Decision: try next=t
               (t
                (incf level)
                (push (mk-te next t level nil) trail))))))))))

;; --- Top-level DPLL ---

(defun dpll (f)
  (cond
    ((== f t)   (values 'sat nil))
    ((== f nil) (values 'unsat nil))
    (t
     (let* ((clauses   (cnf->clauses f))
            (all-atoms (clauses->atoms clauses)))
       (dpll-loop clauses all-atoms)))))


;; =====================================================================
;; Tests
;; =====================================================================

(defun assert-dpll (f expected)
  "Check result matches expected; if SAT, verify the assignment works."
  (multiple-value-bind (result assign) (dpll f)
    (assert (== result expected)
            nil "DPLL on ~a: expected ~a got ~a" f expected result)
    (when (and (== result 'sat) (not (== f t)))
      (assert (verify-sat f assign)
              nil "DPLL SAT but assignment doesn't satisfy ~a" f))
    result))

;; 1. Simple SAT
(assert-dpll '(and (or p q)) 'sat)

;; 2. Simple UNSAT: empty clause
(assert-dpll '(and (or)) 'unsat)

;; 3. BCP-only SAT: forced chain p→q→r
(assert-dpll '(and (or p) (or (not p) q) (or (not q) r)) 'sat)

;; 4. BCP contradiction at level 0
(assert-dpll '(and (or p) (or (not p))) 'unsat)

;; 5. Needs decision + backjump
;;    Classic: {A,B},{¬A,B},{A,¬B},{¬A,¬B} — all 4 sign combos, UNSAT
(assert-dpll '(and (or a b) (or (not a) b) (or a (not b)) (or (not a) (not b))) 'unsat)

;; 6. The L10 slide example
;;    {A,B},{B,C},{¬B,C,D},{¬A,¬X,Y},{¬A,X,Z},{¬A,¬Y,Z},{¬A,X,¬Z},{¬A,¬Y,¬Z}
(assert-dpll
 '(and (or a b) (or b c) (or (not b) c d)
       (or (not a) (not x) y) (or (not a) x z)
       (or (not a) (not y) z) (or (not a) x (not z))
       (or (not a) (not y) (not z)))
 'sat)

;; 7. Pure literal (q only positive) → BCP/pure handles it
(assert-dpll '(and (or p q) (or p r)) 'sat)

;; 8. Unit propagation chain leads to UNSAT via backjumping
(assert-dpll '(and (or p) (or q) (or (not p) (not q))) 'unsat)

;; 9. Compound atoms (foo x), (bar y) treated as propositional variables
(assert-dpll '(and (or (foo x) (bar y)) (or (not (foo x)) (baz z))) 'sat)

;; 10. Tseitin round-trip: encode (and (or p q) (implies r s)), solve with DPLL
(let* ((f   '(and (or p q) (implies r s)))
       (cnf (tseitin f)))
  (assert-dpll cnf 'sat))

;; 11. Satisfiable 4-var instance requiring backtracking
(assert-dpll '(and (or p q) (or (not p) r) (or (not r) s) (or (not s) q)) 'sat)

;; 12. UNSAT 3-var instance (requires non-trivial backjumping)
(assert-dpll '(and (or p q r) (or (not p) q r) (or p (not q) r)
                   (or (not p) (not q) r) (or p q (not r))
                   (or (not p) q (not r)) (or p (not q) (not r))
                   (or (not p) (not q) (not r)))
             'unsat)

;; 13. Verify the satisfying assignment is correct for a multi-clause formula
(multiple-value-bind (result assign)
    (dpll '(and (or p (not q)) (or (not p) r) (or q (not r))))
  (assert (== result 'sat))
  (assert (verify-sat '(and (or p (not q)) (or (not p) r) (or q (not r))) assign)))

;; 14. t and nil edge cases
(assert (== (dpll t)   (values 'sat nil)))
(assert (== (dpll nil) (values 'unsat nil)))
