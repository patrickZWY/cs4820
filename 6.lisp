(load "~/quicklisp/setup.lisp")
(ql:register-local-projects)
(ql:quickload :cl-z3)

(defpackage :hwk6
  (:use :cl :z3))
(in-package :hwk6)

;; Before we do anything, we must start Z3.
(solver-init)

(solver-push)
(z3-assert (x :bool y :bool z :bool)
        (and (=> x (and y z))
             (=> y (and (not x) (not z)))
             (=> (not z) (not y))))

(check-sat)
(get-model-as-assignment)
(solver-pop)


(solver-push)
(z3-assert (x :string y :string z :string p :string q :string)
            (and (= (seq.++ (seq.++ x y) z) (seq.++ p q))
                 (and (>= (str.len x) 2)
                      (>= (str.len y) 2)
                      (>= (str.len z) 2)
                      (>= (str.len p) 2)
                      (>= (str.len q) 2))
                 (= (seq.extract y 0 2) "ab")
                 (= (seq.extract p (- (str.len p) 2) 2) "ba")))

(check-sat)
(get-model-as-assignment)
(solver-pop)

(solver-push)
(z3-assert (x (:seq :bool) y :int)
            (and (>= y 0)
                 (<= y 32)
                 (= (seq.len x) y)
                 (ite (and (>= (seq.len x) 1) (= (seq.nth x 0) true)) 
                      (= 0 (mod (seq.len x) 2))
                      (!= 0 (mod (seq.len x) 2)))))

(check-sat)
(get-model-as-assignment)
(solver-pop)                     

(solver-push)
(z3-assert (a b c :bool n :int)
  (and (>= n 0)
       (<= n 3)
       (= a (= n (+ (ite a 1 0)
                    (ite b 1 0)
                    (ite c 1 0))))
       (= b (= n 1))
       (= c (not (= n 1)))))

(check-sat)
(get-model-as-assignment)
(solver-pop)  


(register-enum-sort :train-sort (f g d))
(solver-push)
(z3-assert (fireman guard driver :train-sort)
        (and
          (distinct fireman guard driver)
        ((_ at-most 1) (!= driver (enumval :train-sort g))
                       (!= fireman (enumval :train-sort d))
                       (= driver (enumval :train-sort d))
                       (!= fireman (enumval :train-sort g)))
                ((_ at-least 1) (!= driver (enumval :train-sort g))
                       (!= fireman (enumval :train-sort d))
                       (= driver (enumval :train-sort d))
                       (!= fireman (enumval :train-sort g))) 
                       )
                       )
(check-sat)
(get-model-as-assignment)
(solver-pop) 

(defun get-3x3-magic-square-var (row col)
  ;; See the Common Lisp HyperSpec for more information about any
  ;; Common Lisp function.
  ;; For example, the documentation for `concatenate` can be found at
  ;; http://clhs.lisp.se/Body/f_concat.htm
  ;; You can also ask SBCL for documentation for a function
  ;; by running (describe #'<function-name>) in the REPL.
  ;; e.g. (describe #'concatenate)
  (intern (concatenate 'string "X" (write-to-string (+ col (* row 3))))))
;;

(get-3x3-magic-square-var 0 0)

(defun 3x3-magic-square-row-sum (row sum-var)
  ;; I'm going to use the loop macro here. This is a very powerful
  ;; macro that allows us to avoid writing helper functions just to
  ;; perform basic loops.
  ;; See the HyperSpec and
  ;; https://gigamonkeys.com/book/loop-for-black-belts.html for more
  ;; information.
  ;; We want to first generate the variables corresponding to each
  ;; cell in this row.
  (let ((row-squares
         (loop for col below 3
               collect (get-3x3-magic-square-var row col))))
    ;; Then, we want to say that the sum of the squares is equal to
    ;; whatever the sum-var is.
    `(= ,sum-var (+ . ,row-squares))))

(3x3-magic-square-row-sum 0 'S)

(defun 3x3-magic-square-col-sum (col sum-var)
  (let ((col-squares
         (loop for row below 3
               collect (get-3x3-magic-square-var row col))))
    `(= ,sum-var (+ . ,col-squares))))
;; Another sanity check...
(3x3-magic-square-col-sum 0 'S)

(defun 3x3-magic-square-row-col-constraints (sum-var)
  (let ((row-constraints (loop for row below 3 collect (3x3-magic-square-row-sum row sum-var)))
        (col-constraints (loop for col below 3 collect (3x3-magic-square-col-sum col sum-var))))
    ;; ,@ splices a list into an S-expression. e.g. `(1 ,@(list 2 3)) = '(1 2 3)
    `(and ,@row-constraints ,@col-constraints)))
;; Great, this is a conjunction of equalities, which is what we expect.
(3x3-magic-square-row-col-constraints 'S)

(defun 3x3-magic-square-var-specs (sum-var)
  (let ((cell-vars (loop for row below 3 append
                         (loop for col below 3 append
                               `(,(get-3x3-magic-square-var row col) :int)))))
    `(,sum-var :int ,@cell-vars)))

(3x3-magic-square-var-specs 'S)

(defun 3x3-magic-square-vars-between-1-and-9 ()
  (cons 'and (loop for row below 3 append
                   (loop for col below 3 append
                         `((>= ,(get-3x3-magic-square-var row col) 1)
                           (<= ,(get-3x3-magic-square-var row col) 9))))))

(solver-push)
(z3-assert-fn (3x3-magic-square-var-specs 'S)
              (3x3-magic-square-row-col-constraints 'S))
(z3-assert-fn (3x3-magic-square-var-specs 'S)
              (3x3-magic-square-vars-between-1-and-9))
(check-sat)

(solver-pop)

(solver-reset)

(defun 3x3-magic-square-forward-diagonal-sum (sum-var)
     (let ((diagonal-squares
               (loop for each below 3
                    collect (get-3x3-magic-square-var each each))))
          `(= ,sum-var (+ . ,diagonal-squares))
          ))

(defun 3x3-magic-square-backward-diagonal-sum (sum-var)
     `(= ,sum-var (+ . ,(get-3x3-magic-square-var 0 2)
                         ,(get-3x3-magic-square-var 1 1)
                         ,(get-3x3-magic-square-var 2 0)
                          )))


(defun 3x3-magic-square-non-trivial ()
     (let ((all-vars
     (loop for row below 3 append
          (loop for col below 3 collect
               (get-3x3-magic-square-var row col)))))
     `(distinct  ,@all-vars)))

(defun 3x3-normal-non-trivial-magic-square-row-col-diagonal-constraints (sum-var)
  (let ((row-constraints (loop for row below 3 collect (3x3-magic-square-row-sum row sum-var)))
        (col-constraints (loop for col below 3 collect (3x3-magic-square-col-sum col sum-var)))
        (forward-diagonal (3x3-magic-square-forward-diagonal-sum sum-var))
        (backward-diagonal (3x3-magic-square-backward-diagonal-sum sum-var)))
    ;; ,@ splices a list into an S-expression. e.g. `(1 ,@(list 2 3)) = '(1 2 3)
    `(and ,@row-constraints ,@col-constraints ,forward-diagonal ,backward-diagonal)))


(solver-push)
(z3-assert-fn (3x3-magic-square-var-specs 'S)
              (3x3-normal-non-trivial-magic-square-row-col-diagonal-constraints 'S))
(z3-assert-fn (3x3-magic-square-var-specs 'S)
              (3x3-magic-square-vars-between-1-and-9))
(z3-assert-fn (3x3-magic-square-var-specs 'S)
              (3x3-magic-square-non-trivial))
              
(check-sat)

(solver-pop)

(solver-reset)

(defun sudoku-row-sum ())