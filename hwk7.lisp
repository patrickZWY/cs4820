#|

run this:
(load this file)
(in-package :tp)
(import 'acl2s-interface-extras::(acl2s-arity))

 Copyright © 2026 by Pete Manolios 
 CS 4820 Fall 2026

 Homework 7.
 Due: 4/18 (Midnight)

 For this assignment, work in groups of 1-3. Send me and the grader
 exactly one solution per team and make sure to follow the submission
 instructions on the course Web page. In particular, make sure that
 the subject of your email submission is "CS 4820 HWK 7".

 The group members are:

 ... (put the names of the group members here)
 
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

 Here are some examples you can try. 

 acl2s-compute is the form you use when you are using ACL2s to compute
 something, e.g., running a function on some input. 

 (acl2s-compute '(+ 1 2))

 acl2s-query is the form you use when you are querying ACL2s, e.g., a
 property without a name. If the property has a name, then that is not
 a query, but an event and you have to use acl2s-event.

 (acl2s-query 'acl2s::(property (p q :all)
                        (iff (=> p q)
                             (v (! p) q))))

 acl2s-arity is a function that determines if f is a function defined
 in ACL2s and if so, its arity (number of arguments). If f is not a
 function, then the arity is nil. Otherwise, the arity is a natural
 number. Note that f can't be a macro.

 (acl2s-arity 'acl2s::app)     ; is nil since app is a macro
 (acl2s-arity 'acl2s::bin-app) ; is 2

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

(import 'acl2s::(acl2s-compute acl2s-query))
(import 'acl2s-interface-extras::(acl2s-arity))


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
    (or      :arity - :identity nil :idem t   :sink t  )
    (not     :arity 1 :identity -   :idem nil :sink -  )
    (implies :arity 2 :identity -   :idem nil :sink -  )
    (iff     :arity - :identity t   :idem nil :sink -  )
    (if      :arity 3 :identity -   :idem nil :sink -  )))

#|

 mapcar is like map. See the common lisp manual.
 In general if you have questions about lisp, ask on Piazza.

|#

(defparameter *p-funs* (mapcar #'car *p-ops*))
(defparameter *fo-quantifiers* '(forall exists))
(defparameter *booleans* '(t nil))
(defparameter *fo-keywords*
  (append *p-funs* *booleans* *fo-quantifiers*))

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

(defun get-alist (k l)
  (cdr (assoc k l :test #'equal)))

(defun get-key (k l)
  (cadr (member k l :test #'equal)))

(defun remove-dups (l)
  (remove-duplicates l :test #'equal))

(defmacro == (x y) `(equal ,x ,y))
(defmacro != (x y) `(not (equal ,x ,y)))

(defun booleanp (x)
  (in x *booleans*))

(defun no-dupsp (l)
  (or (endp l)
      (and (not (in (car l) (cdr l)))
           (no-dupsp (cdr l)))))

(defun pfun-argsp (pop args)
  (and (p-funp pop)
       (let ((arity (get-key :arity (get-alist pop *p-ops*))))
         (and (or (== arity '-)
                  (== (len args) arity))
              (every #'p-formulap args)))))


#|

 Next we have some utilities for converting propositional formulas to
 ACL2s formulas.

|#

(defun to-acl2s (f)
  (match f
    ((type symbol) (intern (symbol-name f) "ACL2S"))
    ((list 'iff) t)
    ((list 'iff p) (to-acl2s p))
    ((list* 'iff args)
     (acl2s::xxxjoin 'acl2s::iff
                     (mapcar #'to-acl2s args)))
    ((cons x xs)
     (mapcar #'to-acl2s f))
    (_ f)))

#|

 A FO term is either a 

 constant symbol: a symbol whose name starts with "C" and is
 optionally followed by a natural number with no leading 0's, e.g., c0,
 c1, c101, c, etc are constant symbols, but c00, c0101, c01, etc are
 not. Notice that (gentemp "C") will create a new constant. Notice
 that symbol names  are case insensitive, so C1 is the same as c1.

 quoted constant: anything of the form (quote object) for any object

 constant object: a rational, boolean, string, character or keyword

 variable: a symbol whose name starts with "X", "Y", "Z", "W", "U" or
 "V" and is optionally followed by a natural number with no leading
 0's (see constant symbol). Notice that (gentemp "X") etc will create
 a new variable.

 function application: (f t1 ... tn), where f is a
 non-constant/non-variable/non-boolean/non-keyword symbol. The arity
 of f is n and every occurrence of (f ...)  in a term or formula has
 to have arity n. Also, if f is a defined function in ACL2s, its arity
 has to match what ACL2s expects. We allow functions of 0-arity.
 
|#

;; symbol-name turns symbol into string
(defun char-nat-symbolp (s chars)
  (and (symbolp s)
       (let ((name (symbol-name s)))
         (and (<= 1 (len name))
              (in (char name 0) chars)
              (or (== 1 (len name))
                  ;; parse-integer will return 1 for 01, making it illegal
                  (let ((i (parse-integer name :start 1 :junk-allowed t)))
                    (and (integerp i)
                         (<= 0 i)
                         (string= (format nil "~a~a" (char name 0) i)
                                  name))))))))

(defun constant-symbolp (s)
  (char-nat-symbolp s '(#\C)))

(defun variable-symbolp (s)
  (char-nat-symbolp s '(#\X #\Y #\Z #\W #\U #\V)))

(defun quotep (c)
  (and (consp c)
       (== (car c) 'quote)))

(defun constant-objectp (c)
  (typep c '(or boolean rational simple-string standard-char keyword)))

#|

Examples

(constant-objectp #\a)
(constant-objectp 0)
(constant-objectp 1/221)
(constant-objectp "hi there")
(constant-objectp t)
(constant-objectp nil)
(constant-objectp :hi)
(constant-objectp 'a)

(quotep '1)  ; recall that '1 is evaluated first
(quotep ''1) ; but this works
(quotep '(1 2 3))  ; similar to above
(quotep ''(1 2 3)) ; similar to above
(quotep (list 'quote (list 1 2 3))) ; verbose version of previous line

|#

(defun function-symbolp (f)
  (and (symbolp f)
       (not (in f *fo-keywords*))
       (not (keywordp f))
       (not (constant-symbolp f))
       (not (variable-symbolp f))))

#|

(function-symbolp 'c)
(function-symbolp 'c0)
(function-symbolp 'c00)
(function-symbolp 'append)
(function-symbolp '+)

|#

(defmacro mv-and (a b &optional (fsig 'fsig) (rsig 'rsig))
  `(if ,a ,b (values nil ,fsig ,rsig)))

(defmacro mv-or (a b &optional (fsig 'fsig) (rsig 'rsig))
  `(if ,a (values t ,fsig ,rsig) ,b))

(defun fo-termp (term &optional (fsig nil) (rsig nil))
  (match term
    ((satisfies constant-symbolp) (values t fsig rsig))
    ((satisfies variable-symbolp) (values t fsig rsig))
    ((satisfies quotep) (values t fsig rsig))
    ((satisfies constant-objectp) (values t fsig rsig))
    ((list* f args)
     (mv-and
      ;; f cannot appear in rsig, because it's not a relation 
      (and (function-symbolp f) (not (get-alist f rsig)))
      ;; f needs correct arity number if appears more than once in fsig
      (let* ((fsig-arity (get-alist f fsig))
             (acl2s-arity
              (or fsig-arity
                  (acl2s-arity (to-acl2s f))))
             (arity (or acl2s-arity (len args)))
             (fsig (if fsig-arity fsig (acons f arity fsig))))
        (mv-and (== arity (len args))
                (fo-termsp args fsig rsig)))))
    (_ (values nil fsig rsig))))

(defun fo-termsp (terms fsig rsig)
  (mv-or (endp terms)
         (let+ (((&values res fsig rsig)
                 (fo-termp (car terms) fsig rsig)))
           (mv-and res
                   (fo-termsp (cdr terms) fsig rsig)))))

#|

Examples

(fo-termp '(f d 2))
(fo-termp '(f c 2))
(fo-termp '(f c0 2))
(fo-termp '(f c00 2))
(fo-termp '(f '1 '2))
(fo-termp '(f (f '1 '2)
              (f v1 c1 '2)))


(fo-termp '(binary-append '1 '2))
(fo-termp '(binary-append '1 '2 '3))
(fo-termp '(binary-+ '1 '2))
(fo-termp '(+ '1 '2)) 
(fo-termp '(- '1 '2))

|#

#|

 A FO atomic formula is either an 

 atomic equality: (= t1 t2), where t1, t2 are FO terms.

 atomic relation: (P t1 ... tn), where P is a
 non-constant/non-variable symbol. The arity of P is n and every
 occurrence of (P ...) has to have arity n. Also, if P is a defined
 function in ACL2s, its arity has to match what ACL2s expects.  We do
 not check that if P is a defined function then it has to return a
 Boolean. Make sure that you do not use such examples.

|#

(defun relation-symbolp (f)
  (function-symbolp f))

#|

Examples

(relation-symbolp '<)
(relation-symbolp '<=)
(relation-symbolp 'binary-+)

|#

(defun fo-atomic-formulap (f &optional (fsig nil) (rsig nil))
  (match f
    ((list '= t1 t2)
     (fo-termsp (list t1 t2) fsig rsig))
    ((list* r args)
     (mv-and 
      ;; r cannot appear in fsig because it's not a function
      (and (relation-symbolp r) (not (get-alist r fsig)))
      (let* ((rsig-arity (get-alist r rsig))
             (acl2s-arity
              (or rsig-arity
                  (acl2s-arity (to-acl2s r))))
             (arity (or acl2s-arity (len args)))
             ;; use original mapping or extend it
             (rsig (if rsig-arity rsig (acons r arity rsig))))
        (mv-and (== arity (len args))
                (fo-termsp args fsig rsig)))))
    (_ (values nil fsig rsig))))

#|
 
 Here is the definition of a propositional formula. We allow
 Booleans.
 
|#

(defun pfun-fo-argsp (pop args fsig rsig)
  (mv-and (p-funp pop)
          (let ((arity (get-key :arity (get-alist pop *p-ops*))))
            (mv-and (or (== arity '-)
                        (== (len args) arity))
                    (fo-formulasp args fsig rsig)))))

(defun p-fo-formulap (f fsig rsig)
  (match f
    ((type boolean) (values t fsig rsig))
    ((list* pop args)
     (if (p-funp pop)
         (pfun-fo-argsp pop args fsig rsig)
       (values nil fsig rsig)))
    (_ (values nil fsig rsig))))

#|
 
 Here is the definition of a quantified formula. 

 The quantified variables can be a variable 
 or a non-empty list of variables with no duplicates.
 Examples include

 (exists w (P w y z x))
 (exists (w) (P w y z x))
 (forall (x y z) (exists w (P w y z x)))

 But this does not work

 (exists c (P w y z x))
 (forall () (exists w (P w y z x)))
 (forall (x y z x) (exists w (P w y z x)))

|#

(defun quant-fo-formulap (f fsig rsig)
  (match f
    ((list q vars body)
     (mv-and (and (in q *fo-quantifiers*)
                      ;; quantifier can be a single element
                  (or (variable-symbolp vars)
                           ;; cannot have empty quantifiers
                      (and (consp vars)
                           ;; cannot have repeated quantifiers
                           (no-dupsp vars)
                           (every #'variable-symbolp vars))))
             (fo-formulap body fsig rsig)))
    (_ (values nil fsig rsig))))

(defun mv-seq-first-fun (l)
  (if (endp (cdr l))
      (car l)
    (let ((res (gensym))
          (f (gensym))
          (r (gensym)))
      `(multiple-value-bind (,res ,f ,r)
           ,(car l)
         (if ,res
             (values t ,f ,r)
           ,(mv-seq-first-fun (cdr l)))))))

(defmacro mv-seq-first (&rest rst)
  (mv-seq-first-fun rst))
  
(defun fo-formulap (f &optional (fsig nil) (rsig nil))
  (mv-seq-first
   (fo-atomic-formulap f fsig rsig)
   (p-fo-formulap f fsig rsig)
   (quant-fo-formulap f fsig rsig)
   (values nil fsig rsig)))

(defun fo-formulasp (fs fsig rsig)
  (mv-or (endp fs)
         (let+ (((&values res fsig rsig)
                 (fo-formulap (car fs) fsig rsig)))
           (mv-and res
                   (fo-formulasp (cdr fs) fsig rsig)))))

#|

 We can use fo-formulasp to find the function and relation
 symbols in a formula as follows.
 
|#

(defun fo-f-symbols (f)
  (let+ (((&values res fsig rsig)
          (fo-formulap f)))
    (mapcar #'car fsig)))

(defun fo-r-symbols (f)
  (let+ (((&values res fsig rsig)
          (fo-formulap f)))
    (mapcar #'car rsig)))

#|

Examples

(fo-formulap 
 '(forall (x y z) (exists w (P w y z x))))

(fo-formulap 
 '(forall (x y z x) (exists w (P w y z x))))

(quant-fo-formulap 
 '(forall (x y z) (exists y (P w y z x))) nil nil)

(fo-formulap
 '(exists w (P w y z x)))

(fo-atomic-formulap
 '(exists w (P w y z x)) nil nil)

(quant-fo-formulap 
 '(exists w (P w y z x)) nil nil)

(fo-formulap 
 '(P w y z x))

(fo-formulap
 '(and (forall (x y z) (or (not (= (q z) (r z))) nil (p '1 x y)))
       (exists w (implies (forall x1 (iff (= (p1 x1 w) c2) (q c1) (r c2)))
                          (p '2 y w)))))

(fo-formulap
 '(forall (x y z) (or (not (= (q z) (r z))) nil (p '1 x y))))

(fo-formulap
 '(exists w (implies (forall x1 (iff (= (p1 x1 w) c2) (q c1) (r c2)))
                          (p '2 y w))))

(fo-formulap
 '(exists w (implies (forall x1 (iff (p1 x1 w) (q c1) (r c2)))
                     (p '2 y w))))

(fo-formulap
 '(and (forall (x y z) (or (not (= (q2 z) (r2 z))) nil (p '1 x y)))
       (exists w (implies (forall x1 (iff (= (p1 x1 w) c2) (q c1) (r c2)))
                          (p '2 y w)))))

(fo-formulap
 '(forall x1 (iff (p1 x1 w) (q c1) (r c2))))

(fo-formulap
 '(iff (p1 x1 w) (q c1) (r c2)))

(fo-atomic-formulap
 '(p1 x1 w))

(variable-symbolp 'c1)
(fo-termp 'x1)
(fo-termp 'w1)
(fo-termp '(x1 w) nil nil)
(fo-termsp '(x1 w) nil nil)

|#

#|
 
 Where appropriate, for the problems below, modify your solutions from
 homework 4. For example, you already implemented most of the
 simplifications in Question 1 in homework 4.
 
|#


#|
 
 Question 1. (25 pts)

 Define function fo-simplify that given a first-order (FO) formula
 returns an equivalent FO formula with the following properties.

 A. The returned formula is either a constant or does not include any
 constants. For example:

 (and (p x) t (q t y) (q y z)) should be simplified to 
 (and (p x) (q t y) (q y z)) 

 (and (p x) t (q t b) nil) should be simplified to nil

 B. Expressions are flattened, e.g.:

 (and (p c) (= c '1) (and (r) (s) (or (r1) (r2)))) is not flat, but this is
 (and (p c) (= c '1) (r) (s) (or (r1) (r2)))

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
 form remain (where f is a formula)
 
 (not (not f))

 E. Simplify formulas so that no subexpressions of the following form
 remain 

 (op ... p ... q ...)

 where p, q are equal literals or  p = (not q) or q = (not p).

 For example
 
 (or (f) (f1) (p a b) (not (p a b)) (= w z)) should be simplified to 

 t 
 
 F. Simplify formulas so there are no vacuous quantified formulas.
 For example, 

 (forall (x w) (P y z))  should be simplified to
 
 (P y z)

 and 

 (forall (x w) (P x y z))  should be simplified to
 
 (forall (x) (P x y z)) 

 G. Simplify formulas by using ACL2s to evaluate, when possible, terms
 of the form (f ...) where f is an ACL2s function all of whose
 arguments are either constant-objects or quoted objects.

 For example,

 (P (binary-+ 4 2) 3)

 should be simplified to

 (P 6 3)

 Hint: use acl2s-compute and to-acl2s. For example, consider

 (acl2s-compute (to-acl2s '(binary-+ 4 2)))

 On the other hand,

 (P (binary-+ 'a 2) 3)

 does not get simplified because 
 
 (acl2s-compute (to-acl2s '(binary-+ 'a 2)))

 indicates an error (contract/guard violation). See the definition of
 acl2s-compute to see how to determine if an error occurred.

 H. Test your definitions using at least 10 interesting formulas.  Use
 the acl2s code, if you find it useful.  Include deeply nested
 formulas, all of the Boolean operators, quantified formulas, etc.

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
 increase the size of a formula. 

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

(defun p-formulap (f)
  (match f
    ((type boolean) t) ; don't need this case, but here for emphasis
    ((type symbol) t)
    ((list* pop args)
     (if (p-funp pop)
         (pfun-argsp pop args)
       t))
    (_ nil)))


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

 Next we have some utilities for converting propositional formulas to
 ACL2s formulas.

|#

(defun nary-to-2ary (fun args)
  (let ((identity (pfun-key->val fun :identity)))
    (match args
      (nil identity)
      ((list x) (to-acl2s x))
      (_ (acl2s::xxxjoin (to-acl2s fun) (mapcar #'to-acl2s args))))))


(defun pvars- (f)
  (match f
    ((type boolean) nil)
    ((type symbol) (list f))
    ((list* op args)
     (and (p-funp op)
          (reduce #'append (mapcar #'pvars- args))))))

(defun pvars (f) (remove-dups (pvars- f)))


(defun boolean-hyps (l)
  (reduce #'append
          (mapcar #'(lambda (x) `(,x :bool))
                  (mapcar #'to-acl2s l))))



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





; So, here's a useful function
(defun assert-acl2s-equal (f g)
  (assert (== (car (acl2s-check-equal f g)) nil)))




; Here is how we can use ACL2s to check our code.
(let* ((x '(or (foo a (g a c)) (g a c) (not (foo a (g a c))))))
  (assert-acl2s-equal x t))

(let* ((x '(or (foo a (g a c)) (g a c) (not (foo a (g a c)))))
       (sx (p-skeleton x)))
  (assert-acl2s-equal sx t))


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

(defun collect-vars (f)
  (cond ((variable-symbolp f) (list f))
        ((consp f) (mapcan #'collect-vars f))
        (t nil)))

(defun simplify-vacuous (f)
  (match f
    ((list q vars body)
     (if (in q *fo-quantifiers*)
         (let* ((varlist (if (listp vars) vars (list vars)))
                (used (intersection varlist (collect-vars body) :test #'equal)))
           (cond ((null used) body)
                 ((== (len used) (len varlist)) f)
                 (t `(,q ,used ,body))))
       f))
    (_ f)))
  
(defun all-constant-args-p (args)
  (every (lambda (a) (or (constant-objectp a) (quotep a))) args))

(defun simplify-acl2s (f)
  (match f
    ((list* fun args)
     (if (and (acl2s-arity (to-acl2s fun))
              (all-constant-args-p args))
         (let ((result (acl2s-compute (to-acl2s f))))
           (if (or (null result) (eq (car result) :error))
               f
             (cadr result)))
       f))
    (_ f)))

(defun p-condition (f env)
  (match f
         ((type boolean) f)
         ((type symbol)
          (let ((hit (assoc f env :test #'equal)))
            (if hit (cdr hit) f)))
         ((list* pop args)
          (if (p-funp pop)
              (fo-simplify (cons pop (mapcar (lambda (x) (p-condition x env)) args)))
              (let ((hit (assoc f env :test #'equal)))
                (if hit (cdr hit) f))))
         (_ f)))

(defun fo-simplify (f)
  (match f
    ((type boolean) f)
    ((type symbol) f)
    ((satisfies quotep) f)
    ((satisfies constant-objectp) f)
    ((list* op args)
      (cond 
      
        ((in op *fo-quantifiers*)
         (let ((simplified-body (fo-simplify (car (last args)))))
             (simplify-vacuous `(,op ,(car args) ,simplified-body))))
        ((p-funp op)
          (let* ((sargs (mapcar #'fo-simplify args))
              (sargs (flatten-op-args op sargs)))
          (case op
           (not
            (let ((a (first sargs)))
              (cond
                ((and (consp a) (== (car a) 'not))  (fo-simplify (cadr a)))  ; re-simplify
                ((and (consp a) (== (car a) 'iff))  (fo-simplify (cons 'xor (cdr a))))  ; re-simplify
                ((and (consp a) (== (car a) 'xor))  (fo-simplify (cons 'iff (cdr a))))  ; re-simplify
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
                (return-from fo-simplify nil))

              (setf sargs (remove t sargs :test #'equal))

              (when (some (lambda (x)
                            (member (negate-lit x) sargs :test #'equal))
                          sargs)
                (return-from fo-simplify nil))

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
                (return-from fo-simplify t))

              (setf sargs (remove nil sargs :test #'equal))

              (when (some (lambda (x)
                            (member (negate-lit x) sargs :test #'equal))
                          sargs)
                (return-from fo-simplify t))

              (make-nary 'or (remove-dups sargs))))

           (implies
            (destructuring-bind (p q) sargs
              (cond ((== p nil) t)
                    ((== p t)   q)
                    ((== q t)   t)
                    ((== q nil) (fo-simplify `(not ,p)))
                    ((== p q)   t)
                    (t          `(implies ,p ,q)))))

           (if
            (destructuring-bind (c tb fb) sargs
              (cond ((== c t)    tb)
                    ((== c nil)  fb)
                    ((== tb fb)  tb)
                    ((== tb t)   (fo-simplify `(or ,c ,fb)))
                    ((== tb nil) (fo-simplify `(and (not ,c) ,fb)))
                    ((== fb t)   (fo-simplify `(or (not ,c) ,tb)))
                    ((== fb nil) (fo-simplify `(and ,c ,tb)))
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
                  (fo-simplify `(not ,base))
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
                  (fo-simplify `(not ,base))
                  base)))
           (otherwise (cons op sargs)))))

          (t
              (let ((computed (simplify-acl2s f)))
                (if (== computed f)
                    (cons op (mapcar #'fo-simplify args))
                    computed)))))

    (_ f)))




#|

 Question 2. (10 pts)

 Define nnf, a function that given a FO formula, something that
 satisfies fo-formulap, puts it into negation normal form (NNF).

 The resulting formula cannot contain any of the following
 propositional connectives: implies, iff, if.

 Test nnf using at least 10 interesting formulas. Make sure you
 support quantification.

|#

(defun nnf (f)
  (match f
    ((type boolean) f)
    ((type symbol) f)
    ((satisfies quotep) f)
    ((satisfies constant-objectp) f)
    ((list 'not a)
      (match a
        ((type boolean) (not a))
        ((list 'not b)  (nnf b))
        ((list* 'and args) (nnf `(or  ,@(mapcar (lambda (x) `(not ,x)) args))))
        ((list* 'or args)  (nnf `(and ,@(mapcar (lambda (x) `(not ,x)) args))))
        ((list 'implies p q) (nnf `(and ,p (not ,q))))
        ((list 'forall vars body) `(exists ,vars ,(nnf `(not ,body))))
        ((list 'exists vars body) `(forall ,vars ,(nnf `(not ,body))))
        (_ `(not ,(nnf a)))))
    ((list 'implies p q) (nnf `(or (not ,p) ,q)))
    ((list 'iff p q) (nnf `(and (or (not ,p) ,q) (or ,p (not ,q)))))
    ((list* op args)
      (let ((nnfed (mapcar #'nnf args)))
        (if (member op '(and or))
            (cons op (apply #'append (mapcar (lambda (a)
                      (if (and (consp a) (== (car a) op))
                          (cdr a)
                          (list a)))
                          nnfed)))
          (cons op nnfed))))
    (_ f)))

#|

 Question 3. (25 pts)

 Define simp-skolem-pnf-cnf, a function that given a FO formula,
 simplifies it using fo-simplify, then puts it into negation normal
 form, applies skolemization, then puts the formula in prenex normal
 form and finally transforms the matrix into an equivalent CNF
 formula.

 To be clear: The formula returned should be equi-satisfiable with the
 input formula, should contain no existential quantifiers, and if it
 has quantifiers it should be of the form

 (forall (...) matrix)

 where matrix is quantifier-free and in CNF. 

 The fewer quantified variables, the better.
 The fewer Skolem functions, the better.
 The smaller the arity of Skolem functions, the better.
 Having said that, correctness should be your primary consideration.

 Test your functions using at least 10 interesting formulas. 
 
|#

(defun subst-term (sigma tm)
  (match tm
    ((type symbol)
      (let ((hit (assoc tm sigma :test #'equal)))
        (if hit (cdr hit) tm)))
    ((satisfies quotep) tm)
    ((satisfies constant-objectp) tm)
    ((list* f args)
      (cons f (mapcar (lambda (a) (subst-term sigma a)) args)))
    (_ tm)
    ))

(defun subst-formula (sigma f)
  (match f
    ((type boolean) f)
    ((type symbol)
      (let ((hit (assoc f sigma :test #'equal)))
        (if hit (cdr hit) f)))
        
    ((satisfies quotep) f)
    ((satisfies constant-objectp) f)
    ((list q vars body)
      (if (member q *fo-quantifiers* :test #'equal)
          (let* ((vs (if (listp vars) vars (list vars)))
                 (sigma1 (remove-if (lambda (pr)
                                      (member (car pr) vs :test #'equal))
                                sigma)))
            `(,q ,vars ,(subst-formula sigma1 body)))
          (list q
                (subst-formula sigma vars)
                (subst-formula sigma body))))
    ((list* op args)
      (cons op (mapcar (lambda (a) (subst-formula sigma a)) args)))
    (_ f)
    ))

(defun variant (base used)
  (let ((sym (intern (string-upcase base))))
    (if (member sym used :test #'equal)
      (variant (concatenate 'string base "0") used)
      sym)))

;; if no universals before, generate constant
;; if universals before, generate functions
(defun mk-skolem-term (y uvars fns)
  (let* ((base (if (endp uvars)
                (format nil "c_~a" y)
              (format nil "f_~a" y)))
            (name (variant base fns)))
          (values
            (if (endp uvars)
                name
              (cons name uvars))
            name)))

(defun skolem-exists-vars (vars body uvars fns)
  (if (endp vars)
      (skolem body uvars fns)
      (multiple-value-bind (term fname)
        (mk-skolem-term (car vars) uvars fns)
      (let* ((body1 (subst-formula (list (cons (car vars) term)) body)))
      (skolem-exists-vars (cdr vars) body1 uvars (cons fname fns))))))

(defun skolem-list (args uvars fns)
  (if (endp args)
      (values nil fns)
    (multiple-value-bind (a1 fns1)
        (skolem (car args) uvars fns)
      (multiple-value-bind (rest1 fns2)
          (skolem-list (cdr args) uvars fns1)
            (values (cons a1 rest1) fns2)))))

;; at this point, we have done simplification so
;; all existential quantifiers are used in body
;; and no empty quantifier existentials
;; similarly for universal quantifiers
(defun skolem (fm &optional (uvars nil) (fns nil))
  (match fm
    ((list 'forall vars body)
        (let ((vs (if (listp vars) vars (list vars))))
          (multiple-value-bind (body1 fns1)
            (skolem body (append uvars vs) fns)
          (values `(forall ,vars ,body1) fns1))))

    ((list 'exists vars body)
        (skolem-exists-vars (if (listp vars) vars (list vars))
                            body
                            uvars
                            fns))

    ((list* op args)
          (multiple-value-bind (args1 fns1)
            (skolem-list args uvars fns)
          (values (cons op args1) fns1)))

        (_ (values fm fns))))

(defun conjunction-p (f)
  (and (consp f) (eq (car f) 'and)))

(defun disjunction-p (f)
  (and (consp f) (eq (car f) 'or)))

(defun make-and (args)
  (let ((xs (flatten-and args)))
    (cond
      ((endp xs) t)
      ((endp (cdr xs)) (car xs))
      (t (cons 'and xs)))))

(defun make-or (args)
  (let ((xs (flatten-or args)))
    (cond
      ((endp xs) nil)
      ((endp (cdr xs)) (car xs))
      (t (cons 'or xs)))))

(defun flatten-and (args)
  (apply #'append
    (mapcar (lambda (a)
      (if (conjunction-p a)
          (cdr a)
          (list a)))
        args)))

(defun flatten-or (args)
  (apply #'append
    (mapcar (lambda (a)
              (if (disjunction-p a)
                  (cdr a)
                  (list a)))
                args)))

(defun drop-foralls (fm)
  (match fm 
    ((list 'forall vars body)
      (declare (ignore vars))
      (drop-foralls body))
    ((list 'not a)
        `(not ,(drop-foralls a)))
    ((list* 'and args)
      (make-and (mapcar #'drop-foralls args)))

    ((list* 'or args)
      (make-or (mapcar #'drop-foralls args)))

    (_ fm)))

(defun distribute-or-2 (a b)
  (cond
    ((conjunction-p a)
      (make-and 
        (mapcar (lambda (x)
                (distribute-or-2 x b))
                (cdr a))))

    ((conjunction-p b)
      (make-and
        (mapcar (lambda (y)
                (distribute-or-2 a y))
                (cdr b))))
    (t
      (make-or (flatten-or (list a b))))))

(defun distribute-or-list (args)
  (cond
    ((endp args) nil)
    ((endp (cdr args)) (car args))
    (t (distribute-or-2 (car args)
                        (distribute-or-list (cdr args))))))

(defun cnf (fm)
  (let ((fm1 (drop-foralls fm)))
    (cnf1 fm1)))

(defun cnf1 (fm)
  (match fm
    ((list* 'and args)
      (make-and
        (flatten-and
          (mapcar #'cnf1 args))))
          
    ((list* 'or args)
      (distribute-or-list 
        (mapcar #'cnf1 args)))
        
    ((list 'not a)
      `(not ,a))
      
    (_ fm)))

(defun simp-skolem-pnf-cnf (f)
  (multiple-value-bind (sk fns)
    (skolem (nnf (fo-simplify f)))
  (declare (ignore fns))
  (cnf sk)))


#|

 Question 4. (15 pts)

 Define unify, a function that given an a non-empty list of pairs,
 where every element of the pair is FO-term, returns an mgu (most
 general unifier) if one exists or the symbol 'fail otherwise.

 An assignment is a list of conses, where car is a variable, the cdr
 is a term and the variables (in the cars) are unique.

 Test your functions using at least 10 interesting inputs. 
 
|#
;; occurs check
(defun defined (env x)
  (not (null (assoc x env :test #'equal))))

(defun apply-subst (env tm)
  (match tm
    ((satisfies variable-symbolp)
     (let ((hit (assoc tm env :test #'equal)))
       (if hit
           (apply-subst env (cdr hit))
           tm)))
    ((satisfies quotep) tm)
    ((satisfies constant-objectp) tm)
    ((list* f args)
     (cons f (mapcar (lambda (a) (apply-subst env a)) args)))
    (_ tm)))

(defun istriv (env x tm)
  (match tm
    ((satisfies variable-symbolp)
     (or (equal tm x)
         (and (defined env tm)
              (istriv env x (apply-subst env tm)))))
    ((list* f args)
     (declare (ignore f))
     (if (some (lambda (a) (istriv env x a)) args)
         (error "cyclic")
         nil))
    (_ nil)))

(defun unify-helper (env eqs)
  (match eqs
    (nil env)
    ((cons (list lhs rhs) oth)
     (let ((lhs (apply-subst env lhs))
           (rhs (apply-subst env rhs)))
       (match (list lhs rhs)

         ((list (list* f fargs) (list* g gargs))
          (if (and (equal f g)
                   (= (length fargs) (length gargs)))
              (unify-helper env (append (mapcar #'list fargs gargs) oth))
              (error "impossible unification")))

         ((list (satisfies variable-symbolp) tm)
          (let ((x lhs))
            (istriv env x tm)
            (unify-helper (acons x tm env) oth)))

         ((list tm (satisfies variable-symbolp))
          (let ((x rhs))
            (istriv env x tm)
            (unify-helper (acons x tm env) oth)))

         (_
          (if (equal lhs rhs)
              (unify-helper env oth)
              (error "impossible unification"))))))))

(defun unify (l)
  (handler-case
      (let ((env (unify-helper nil l)))
        (mapcar (lambda (pr)
                  (cons (car pr)
                        (apply-subst env (cdr pr))))
                env))
    (error () 'fail)))
#|

 Question 5. (25 pts)

 Define fo-no=-val, a function that given a FO formula, without equality,
 checks if it is valid using U-Resolution.

 If it is valid, return 'valid.

 Your code should use positive resolution and must implement
 subsumption and replacement.

 Test your functions using at least 10 interesting inputs
 including the formulas from the following pages of the book: 178
 (p38, p34), 179 (ewd1062), 180 (barb), and 198 (the Los formula).


|#

;;(defun fo-no=-val (f) ...)

#|

 Question 6. Extra Credit (20 pts)

 Define fo-val, a function that given a FO formula, checks if it is
 valid using U-Resolution.

 If it is valid, return 'valid.

 Your code should use positive resolution and must implement
 subsumption and replacement. This is an extension of question 5,
 where you replace equality with a new relation symbol and add
 the appropriate equivalence and congruence hypotheses.

|#

;;(defun fo-val (f) ...)

