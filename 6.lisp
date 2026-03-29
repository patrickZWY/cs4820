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
  (intern (concatenate 'string "X" (write-to-string (+ col (* row 3))))))

(get-3x3-magic-square-var 0 0)

(defun 3x3-magic-square-row-sum (row sum-var)
  (let ((row-squares
         (loop for col below 3
               collect (get-3x3-magic-square-var row col))))
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
  (let ((diagonal-squares
         (list (get-3x3-magic-square-var 0 2)
               (get-3x3-magic-square-var 1 1)
               (get-3x3-magic-square-var 2 0))))
    `(= ,sum-var (+ . ,diagonal-squares))))


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

(defun sudoku-cell-var (row col val)
  (intern (concatenate 'string "X" (write-to-string (+ col (* row 9))) "_" (write-to-string val))))



;; I have provided some utilities for pretty-printing Sudoku solutions
;; below.

(defun assoc-equal (x a)
  (assoc x a :test #'equal))

;; Given a solution that is an alist from cell vars to booleans, get
;; the assigned value for the cell at the given row and column, or nil
;; if it is unassigned.
(defun get-square-value (soln row col)
  (block outer
    (loop for i from 1 to 9
          do (when (and (cdr (assoc-equal (sudoku-cell-var row col i) soln))
                        (cadr (assoc-equal (sudoku-cell-var row col i) soln)))
               (return-from outer i)))
    nil))



;; This pretty-prints a Sudoku solution, using `get-square-value` to
;; handle the task of getting the value of a cell from the solution
;; representation used.
(defun pretty-print-3x3-sudoku-solution (soln)
  (loop for row below 9
        do (progn (terpri)
                  (loop for col below 9
                        do (progn (format t "~A " (get-square-value soln row col))
                                  (when (equal (mod col 3) 2) (format t "  "))))
                  (when (equal (mod row 3) 2) (terpri)))))

;; Here's an example starting board. It has a unique solution.
(defconstant *sudoku-example-board*
  '(7 _ _   _ 1 _   _ _ _
    _ 1 _   _ _ 3   7 _ 8
    _ 5 3   _ _ _   _ _ 4

    5 _ 9   3 _ _   _ _ 2
    4 _ 1   2 6 _   3 7 _
    _ _ 7   _ 8 5   9 4 _

    2 7 _   _ 9 4   _ 3 _
    8 _ _   5 _ 1   _ 6 _
    _ 3 _   _ _ 2   4 5 _))



;; Here's its solution.
#|
 7 4 8   9 1 6   5 2 3
 6 1 2   4 5 3   7 9 8
 9 5 3   7 2 8   6 1 4

 5 6 9   3 4 7   1 8 2
 4 8 1   2 6 9   3 7 5
 3 2 7   1 8 5   9 4 6

 2 7 5   6 9 4   8 3 1
 8 9 4   5 3 1   2 6 7
 1 3 6   8 7 2   4 5 9
|#

(defun sudoku-cell-vars (row col)
  (loop for val from 1 to 9
      collect (sudoku-cell-var row col val)))



(defun sudoku-exactly-one (vars)
  `(and ((_ at-least 1) ,@vars)
        ((_ at-most 1) ,@vars)))





(defun sudoku-cell-constraints ()
  (cons 'and 
         (loop for row below 9 append
            (loop for col below 9
              collect (sudoku-exactly-one
                        (sudoku-cell-vars row col))))))


(defun sudoku-row-value-vars (row val)
  (loop for col below 9
      collect (sudoku-cell-var row col val)))



(defun sudoku-row-constraints ()
  (cons 'and
      (loop for row below 9 append
        (loop for val from 1 to 9
          collect (sudoku-exactly-one
                    (sudoku-row-value-vars row val))))))



(defun sudoku-col-value-vars (col val)
  (loop for row below 9
    collect (sudoku-cell-var row col val)))


(defun sudoku-col-constraints ()
  (cons 'and
      (loop for col below 9 append
        (loop for val from 1 to 9
            collect (sudoku-exactly-one
                      (sudoku-col-value-vars col val))))))



(defun sudoku-box-value-vars (box-row box-col val)
    (loop for row from (* 3 box-row) below (+ (* 3 box-row) 3) append
        (loop for col from (* 3 box-col) below (+ (* 3 box-col) 3)
            collect (sudoku-cell-var row col val))))

(defun sudoku-box-constraints ()
  (cons 'and
      (loop for box-row below 3 append
          (loop for box-col below 3 append
              (loop for val from 1 to 9
                  collect (sudoku-exactly-one
                              (sudoku-box-value-vars box-row box-col val)))))))



(defun sudoku-starting-board-constraints (input-grid)
    (cons 'and
        (loop for entry in input-grid 
              for idx from 0
              unless (equal entry '_)
                collect (sudoku-cell-var (floor idx 9)
                                          (mod idx 9)
                                          entry))))



(defun sudoku-var-specs ()
  (loop for row below 9 append
      (loop for col below 9 append
          (loop for val from 1 to 9 append
             `(,(sudoku-cell-var row col val) :bool)))))



(defun solve-sudoku (input-grid)
  (let ((var-specs (sudoku-var-specs)))
    (solver-push)
    (z3-assert-fn var-specs (sudoku-cell-constraints))
    (z3-assert-fn var-specs (sudoku-row-constraints))
    (z3-assert-fn var-specs (sudoku-col-constraints))
    (z3-assert-fn var-specs (sudoku-box-constraints))
    (z3-assert-fn var-specs (sudoku-starting-board-constraints input-grid))
    (let ((res (check-sat)))
      (prog1
          (if (or (equal res 'SAT)
                  (equal res :SAT)
                  (equal res 'sat)
                  (equal res :sat))
                (get-model-as-assignment)
                'UNSAT)
              (solver-pop)))))





;; This should print out the solution given above.
(pretty-print-3x3-sudoku-solution (time (solve-sudoku *sudoku-example-board*)))


;; unruly is NP-hard but it is easy to encode hehe
;; basically encode it like we encode sudoku
;; 8x8 board
;; then we only have black or white so i encode black as 1 and white as 2
;; then we encode constraints: each row or col must have 4 black and 4 white
;; and no consecutive 3 for black or white is even easier, we literally start
;; counting one by one until there is not enough items on the same row (like col 6)
;; finally we encode the board and boom it is done
;; i don't want to write too many examples so one example you can just have everything
;; as empty so we start with an empty board
;; second instance we can have an obviously unsat board with consecutive 3 white or black
;; for a working example, see the board i supplied as example, it is taken from the website
;; so it definitely works and our solution gives an answer
;; chatgpt usage about 10 percent


(defun unruly-cell-var (row col val)
  (intern (concatenate 'string "X" (write-to-string (+ col (* row 8))) "_" (write-to-string val))))

(defun get-unruly-value (soln row col)
    (cond
      ((cadr (assoc-equal (unruly-cell-var row col 1) soln)) 1)
      ((cadr (assoc-equal (unruly-cell-var row col 2) soln)) 2)
      (t '_)))

(defun pretty-print-unruly (soln)
  (loop for row below 8 do
      (progn
          (terpri)
          (loop for col below 8 do
              (format t "~A " (get-unruly-value soln row col))))))

(defun unruly-cell-vars (row col)
  (loop for val from 1 to 2
      collect (unruly-cell-var row col val)))


(defconstant *unruly-example-board*
  '(_ _ _ _  _ _ _ 1
    1 _ 1 2  _ 2 _ 1
    _ _ _ 2  _ 2 _ _ 
    _ _ _ _  _ _ _ 2
    1 1 _ _  _ _ _ _ 
    1 _ 2 _  _ 1 _ _
    _ _ _ _  _ _ 1 _ 
    _ 2 _ _  _ _ 2 _
  ))

(defun unruly-exactly-one (vars)
  `(and ((_ at-least 1) ,@vars)
        ((_ at-most 1) ,@vars)))

(defun unruly-exactly-four (vars)
  `(and ((_ at-least 4) ,@vars)
        ((_ at-most 4) ,@vars)))


;; each cell in unruly can only have 1 or 2
(defun unruly-cell-constraints ()
  (cons 'and
          (loop for row below 8 append
            (loop for col below 8
              collect (unruly-exactly-one
                        (unruly-cell-vars row col))))))


;; each row in unruly must have 4 1s and 4 2s
(defun unruly-row-value-vars (row val)
  (loop for col below 8
      collect (unruly-cell-var row col val)))

(defun unruly-row-constraints ()
  (cons 'and
    (loop for row below 8 append
      (loop for val from 1 to 2
        collect (unruly-exactly-four
                  (unruly-row-value-vars row val))))))


(defun unruly-col-value-vars (col val)
  (loop for row below 8
    collect (unruly-cell-var row col val)))

(defun unruly-col-constraints ()
  (cons 'and
      (loop for col below 8 append
        (loop for val from 1 to 2
            collect (unruly-exactly-four
                      (unruly-col-value-vars col val))))))

;; for consecutive 3s, row 0 to 5 cannot have consecutive
(defun consecutive-row-constraints ()
  (cons 'and
      (loop for row below 8 append
        (loop for col from 0 to 5 append
            (list
                `(not (and ,(unruly-cell-var row col 1)
                           ,(unruly-cell-var row (+ col 1) 1)
                           ,(unruly-cell-var row (+ col 2) 1)))
                `(not (and ,(unruly-cell-var row col 2)
                           ,(unruly-cell-var row (+ col 1) 2)
                           ,(unruly-cell-var row (+ col 2) 2))))))))

(defun consecutive-col-constraints ()
  (cons 'and
      (loop for col below 8 append
        (loop for row from 0 to 5 append
            (list
                `(not (and ,(unruly-cell-var row col 1)
                           ,(unruly-cell-var (+ row 1) col 1)
                           ,(unruly-cell-var (+ row 2) col 1)))
                `(not (and ,(unruly-cell-var row col 2)
                           ,(unruly-cell-var (+ row 1) col 2)
                           ,(unruly-cell-var (+ row 2) col 2))))))))

(defun unruly-starting-board-constraints (input-grid)
    (cons 'and
        (loop for entry in input-grid
              for idx from 0
              unless (equal entry '_)
                collect (unruly-cell-var (floor idx 8)
                                         (mod idx 8)
                                         entry))))

(defun unruly-var-specs ()
  (loop for row below 8 append 
    (loop for col below 8 append
      (loop for val from 1 to 2 append
        `(,(unruly-cell-var row col val) :bool)))))

(defun solve-unruly (input-grid)
  (let ((var-specs (unruly-var-specs)))
      (solver-push)
      (z3-assert-fn var-specs (unruly-cell-constraints))
      (z3-assert-fn var-specs (unruly-row-constraints))
      (z3-assert-fn var-specs (unruly-col-constraints))
      (z3-assert-fn var-specs (consecutive-row-constraints))
      (z3-assert-fn var-specs (consecutive-col-constraints))
      (z3-assert-fn var-specs (unruly-starting-board-constraints input-grid))
        (let ((res (check-sat)))
            (prog1 
                (if (member res '(SAT :SAT sat :sat))
                    (get-model-as-assignment)
                    'UNSAT)
                  (solver-pop)))))


(pretty-print-unruly (time (solve-unruly *unruly-example-board*)))