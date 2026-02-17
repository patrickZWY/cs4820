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

(definec ack (n m :nat) :pos
  :skip-tests t ; ack is slow, so skip testing
  (match (list n m)
    ((0 &) (1+ m))
    ((& 0) (ack (1- n) 1))
    (& (ack (1- n) (ack n (1- m))))))
; Q2a.  We are using the definition on page 129.
; Q2b. Further-generalized measure for ack (returns a lex)
; Using lex = (oneof nat (cons nat (listof nat))) and ordering l<
; (see “Further Generalized Measure Function Definition”) :contentReference[oaicite:1]{index=1}

(definec m-ack (n m :nat) :lex
  (list n m))

(property (n m :nat)
  (implies (and (not (zp n))
                (zp m))
           (l< (m-ack (1- n) 1)
               (m-ack n m))))

(property (n m :nat)
  (implies (and (not (zp n))
                (not (zp m)))
           (l< (m-ack n (1- m))
               (m-ack n m))))

(property (n m :nat)
  (implies (and (not (zp n))
                (not (zp m)))
           (l< (m-ack (1- n) (ack n (1- m)))
               (m-ack n m))))


