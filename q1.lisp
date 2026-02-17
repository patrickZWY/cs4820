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
;; 70 percent usage of Codex to help with theorem proving
#|
[1,2,3] [4,5] []
-> bad-app [1,2,3] nil [4,5]
-> bad-app nil [1,2,3] [4,5]
-> bad-app nil [2,3] [1,4,5]
...
-> bad-app nil [] [3,2,1,4,5]
-> [3,2,1,4,5]

|#
(definec bad-app (x y acc :tl) :tl
  (match (list x y)
    ((nil nil) acc)
    ((& nil) (bad-app y x acc))
    ((nil (f . r)) (bad-app x r (cons f acc)))
    (& (bad-app x nil (bad-app acc nil y)))))

; Q1a. We are using the definition on page 125
#|
(definec m-bad-app (x y :tl) :nat
  (+ (len x) (len y)))
|#
(definec m-bad-app (x y :tl acc :all) :nat
  (match (list x y)
      ((nil nil) 0)
      ((& nil) (+ 1 (len x)))
      ((nil &) (len y))
      (& (+ 2 (len acc) (len x)))))

; in case 2, swap happens
(property case1-terminate (x acc :tl)
  :hyps (and (consp x))
  :body (< (m-bad-app nil x acc)
	   (m-bad-app x nil acc)))

; in case 3, keep recursing and pushing into acc
(property case2-terminate (f :all acc r :tl)
  :body (< (m-bad-app nil r (cons f acc))
	   (m-bad-app nil (cons f r) acc)))

; in case 4, inner recursive call decrements
(property case3-terminate (x y acc :tl)
  :hyps (and (consp x) (consp y))
  :body (< (m-bad-app acc nil y)
	   (m-bad-app x y acc)))

; in case 4, outer recursive call decreases
(property case4-terminate (x y acc res :tl)
  :hyps (and (consp x) (consp y))
  :body (< (m-bad-app x nil res)
	   (m-bad-app x y acc)))


(property rev-cdr+car (x :cons)
  (== (append (rev (cdr x)) (list (car x)))
      (rev x)))

(property bad-app-nil-is-revappend (y acc :tl)
  (== (bad-app nil y acc)
      (revappend y acc))
  :hints (("Goal"
           :in-theory (e/d (bad-app revappend)
                           (acl2::revappend-removal))
           :do-not '(generalize eliminate-destructors fertilize)
           :induct (revappend y acc))))


(property (x y :tl)
    (== (bad-app x y nil)
     (if (endp x)
         (rev y)
         (if (endp y)
             (rev x)
             (app (rev x) y)))))


       

