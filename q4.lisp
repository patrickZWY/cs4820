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
 Zheng Wangyuan
 Christopher Wright-Williams

|#





(in-PACKAGE "ACL2S")
(SET-GAG-MODE NIL)
(MODELING-ADMIT-ALL)

#|                                                                              
                                                                                
 Q4. We will now reason about sorting algorithms. Consider the                  
 following definitions for insert sort and quicksort.                           
                                                                                
|#

;; See the documentation for <<, which is a total order on the ACL2s            
;; universe, so we can compare anything, no matter the types. This              
;; allows us to define sorting algorithms that work on integers,                
;; rationals, strings, whatever (but using the << ordering).                    

(definec <<= (x y :all) :bool
  (or (== x y)
      (<< x y)))

(definec insert (a :all x :tl) :tl
  (match x
    (() (list a))
    ((e . es) (if (<<= a e)
                  (cons a x)
                (cons e (insert a es))))))

(definec isort (x :tl) :tl
  (match x
    (() ())
    ((e . es) (insert e (isort es)))))

;; find all elements in a list that is smaller than a
(definec less (a :all x :tl) :tl
  (match x
    (() ())
    ((e . es) (if (<< e a)
                  (cons e (less a es))
                (less a es)))))

;; find all elements in a list that is not smaller than a
(definec notless (a :all x :tl) :tl
  (match x
    (() ())
    ((e . es) (if (<<= a e)
                  (cons e (notless a es))
                (notless a es)))))

(definec qsort (x :tl) :tl
  (match x
    (() ())
    ((e . es) (app (qsort (less e es))
                   (list e)
                   (qsort (notless e es))))))

;; we need to describe that elements in an isorted list are ordered
(definec orderedp (x :tl) :boolean
  (or (endp x)
      (endp (cdr x))
      (^ (<<= (first x) (second x))
         (orderedp (cdr x)))))

; We need the lemma that insert preserves order to avoid nested
; induction in later lemmas
(property insert-preserves-order (l :tl a :all)
          :h (orderedp l)
          :b (orderedp (insert a l)))

(property isort-ordered (l :tl)
          (orderedp (isort l)))

; Helper lemma from checkpoint
(property less-insert-<<= (l :tl a :all b :all)
          :h (<<= a b)
          :b (== (less a (insert b l))
                 (less a l)))

; We need the invariant that l is ordered
(property less-insert-<< (l :tl a :all b :all)
          :h (^ (<< b a)
                (orderedp l))
          :b (== (less a (insert b l))
                 (insert b (less a l))))

; Lemma 1
(property isort-less (l :tl a :all)
          (== (isort (less a l))
              (less a (isort l))))

; Helper lemmas for Lemma 2 (symmetric from Lemma 1)
(property notless-insert-<<= (l :tl a :all b :all)
          :h (<<= a b)
          :b (== (insert b (notless a l))
                 (notless a (insert b l))))

; Helper lemma
(property notless-insert-<< (l :tl a :all b :all)
          :h (<< b a)
          :b (== (notless a (insert b l))
                 (notless a l)))

; Lemma 2
(property isort-notless (l :tl a :all)
          (== (isort (notless a l))
              (notless a (isort l))))

; Helper lemma
(property orderedp-<=-less (l :tl a :all)
          :h (^ (orderedp l) (<<= a (first l)))
          :b (== (less a l) nil))

; Lemma 3
(property app-less-not-less (l :tl a :all)
          :h (orderedp l)
          :b (== (append (less a l)
                         (cons a (notless a l)))
                 (insert a l)))

; Bridge lemma in the same app-shape used by qsort checkpoints
(property app-less-not-less-app (l :tl a :all)
          :h (orderedp l)
          :b (== (app (less a l)
                      (cons a (notless a l)))
                 (insert a l)))

#|                                                                              
                                                                                
 Q4. Prove the following property.                                              
                                                                                
 This is not easy, so I strongly recommend that you come up with a              
 plan and use the professional method to sketch out a proof.                    
                                                                                
|#

(property qsort=isort (x :tl)
  (== (qsort x)
      (isort x)))
