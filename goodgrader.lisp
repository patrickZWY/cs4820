;;;; ============================================================
;;;; Carry-adder / multiplier generator rewritten for the grader
;;;; Assumes the homework/grader code is already loaded, especially:
;;;;   p-formulap, p-simplify, mk-and helper ok if redefined, etc.
;;;; Package expected: :tp
;;;; ============================================================

(in-package :tp)

;;; ------------------------------------------------------------
;;; Basic formula constructors in the grader's AST dialect
;;; ------------------------------------------------------------

(defun mk-not (p)
  `(not ,p))

(defun mk-and (p q)
  `(and ,p ,q))

(defun mk-or (p q)
  `(or ,p ,q))

(defun mk-imp (p q)
  `(implies ,p ,q))

(defun mk-iff (p q)
  `(iff ,p ,q))

(defun list-conj (l)
  (if (null l) t (reduce #'mk-and l)))

(defun conjoin (f l)
  (list-conj (mapcar f l)))

(defun end-itlist (f l)
  (cond
    ((null l) (error "end-itlist"))
    ((null (cdr l)) (car l))
    (t (funcall f (car l) (end-itlist f (cdr l))))))

;;; ------------------------------------------------------------
;;; Indexed propositional variable generators
;;; Each mk-index returns a closure.
;;; ------------------------------------------------------------

(defun mk-index (name)
  (lambda (i)
    (intern (format nil "P9~A_~A" name i) *package*)))

(defun mk-index2 (name)
  (lambda (i j)
    (intern (format nil "P9~A_~A_~A" name i j) *package*)))

(defun offset (k f)
  (lambda (i)
    (funcall f (+ k i))))

(defun offset2 (k f)
  (lambda (i j)
    (funcall f (+ k i) j)))

;;; ------------------------------------------------------------
;;; Adder primitives
;;; ------------------------------------------------------------

(defun halfsum (x y)
  ;; Original source used Iff(x, Not y)
  (mk-iff x (mk-not y)))

(defun halfcarry (x y)
  (mk-and x y))

(defun ha (x y s c)
  (mk-and (mk-iff s (halfsum x y))
          (mk-iff c (halfcarry x y))))

(defun carry (x y z)
  (mk-or (mk-and x y)
         (mk-and (mk-or x y) z)))

(defun sum (x y z)
  (halfsum (halfsum x y) z))

(defun fa (x y z s c)
  (mk-and (mk-iff s (sum x y z))
          (mk-iff c (carry x y z))))

;;; ------------------------------------------------------------
;;; Ripple-carry adder family
;;; x, y, c, out are closures taking one integer argument.
;;; c is the carry line, with c(i) = carry-in to stage i.
;;; out(i) is the sum bit at stage i.
;;; c(i+1) is the carry-out.
;;; ------------------------------------------------------------

(defun ripplecarry (x y c out n)
  (conjoin
   (lambda (i)
     (fa (funcall x i)
         (funcall y i)
         (funcall c i)
         (funcall out i)
         (funcall c (+ i 1))))
   (loop for i from 0 below n collect i)))

(defun ripplecarry0 (x y c out n)
  (p-simplify
   (ripplecarry x y
                (lambda (i)
                  (if (zerop i) nil (funcall c i)))
                out
                n)))

(defun ripplecarry1 (x y c out n)
  (p-simplify
   (ripplecarry x y
                (lambda (i)
                  (if (zerop i) t (funcall c i)))
                out
                n)))

;;; ------------------------------------------------------------
;;; Multiplexer and carry-select adder
;;; ------------------------------------------------------------

(defun mux (sel in0 in1)
  (mk-or (mk-and (mk-not sel) in0)
         (mk-and sel in1)))

(defun carryselect (x y c0 c1 s0 s1 c s n k)
  (let* ((k* (min n k))
         (fm (mk-and
              (mk-and (ripplecarry0 x y c0 s0 k*)
                      (ripplecarry1 x y c1 s1 k*))
              (mk-and
               (mk-iff (funcall c k*)
                       (mux (funcall c 0)
                            (funcall c0 k*)
                            (funcall c1 k*)))
               (conjoin
                (lambda (i)
                  (mk-iff (funcall s i)
                          (mux (funcall c 0)
                               (funcall s0 i)
                               (funcall s1 i))))
                (loop for i from 0 below k* collect i))))))
    (if (< k* k)
        fm
        (mk-and
         fm
         (carryselect (offset k x)
                      (offset k y)
                      (offset k c0)
                      (offset k c1)
                      (offset k s0)
                      (offset k s1)
                      (offset k c)
                      (offset k s)
                      (- n k)
                      k)))))

(defun mk-adder-test (n k)
  (destructuring-bind (x y c s c0 s0 c1 s1 c2 s2)
      (mapcar #'mk-index '("x" "y" "c" "s" "c0" "s0" "c1" "s1" "c2" "s2"))
    (mk-imp
     (mk-and
      (mk-and (carryselect x y c0 c1 s0 s1 c s n k)
              (mk-not (funcall c 0)))
      (ripplecarry0 x y c2 s2 n))
     (mk-and
      (mk-iff (funcall c n) (funcall c2 n))
      (conjoin
       (lambda (i)
         (mk-iff (funcall s i) (funcall s2 i)))
       (loop for i from 0 below n collect i))))))

;;; ------------------------------------------------------------
;;; Multiplier support
;;; ------------------------------------------------------------

(defun rippleshift (u v c z w n)
  ;; Mirrors the structure of the source:
  ;; ripplecarry0 u v adjusted-c adjusted-out n
  (ripplecarry0
   u
   v
   (lambda (i)
     (if (= i n)
         (funcall w (- n 1))
         (funcall c (+ i 1))))
   (lambda (i)
     (if (zerop i)
         z
         (funcall w (- i 1))))
   n))

(defun multiplier (x u v out n)
  ;; x is a 2-argument closure
  ;; u, v, out are intended as indexed families; u and v may themselves
  ;; denote rows/buses from the original construction.
  ;;
  ;; This is a close structural rewrite of the user's source rather than
  ;; a mathematically re-derived multiplier.
  (if (= n 1)
      (mk-and (mk-iff (funcall out 0) (funcall x 0 0))
              (mk-not (funcall out 1)))
      (p-simplify
       (mk-and
        (mk-iff (funcall out 0) (funcall x 0 0))
        (mk-and
         (rippleshift
          (lambda (i)
            (if (= i (- n 1))
                nil
                (funcall x 0 (+ i 1))))
          (lambda (i)
            (funcall x 1 i))
          (lambda (i)
            (funcall v 2 i))
          (funcall out 1)
          (lambda (i)
            (funcall u 2 i))
          n)
         (if (= n 2)
             (mk-and
              (mk-iff (funcall out 2) (funcall u 2 0))
              (mk-iff (funcall out 3) (funcall u 2 1)))
             (conjoin
              (lambda (k)
                (rippleshift
                 (lambda (i)
                   (funcall u k i))
                 (lambda (i)
                   (funcall x k i))
                 (lambda (i)
                   (funcall v (+ 1 k) i))
                 (funcall out k)
                 (if (= k (- n 1))
                     (lambda (i)
                       (funcall out (+ n i)))
                     (lambda (i)
                       (funcall u (+ k 1) i)))
                 n))
              (loop for k from 2 below n collect k))))))))

;;; ------------------------------------------------------------
;;; Integer/bit helpers
;;; ------------------------------------------------------------

(defun bitlength (x)
  (if (zerop x)
      0
      (+ 1 (bitlength (floor x 2)))))

(defun bit-of (n x)
  (if (zerop n)
      (= 1 (mod x 2))
      (bit-of (- n 1) (floor x 2))))

(defun congruent-to (x m n)
  ;; x is a 1-arg closure
  ;; emit x(i) when bit i of m is 1, else (not x(i))
  (conjoin
   (lambda (i)
     (if (bit-of i m)
         (funcall x i)
         (mk-not (funcall x i))))
   (loop for i from 0 below n collect i)))

(defun prime (p)
  (destructuring-bind (x y out)
      (mapcar #'mk-index '("x" "y" "out"))
    (destructuring-bind (u v)
        (mapcar #'mk-index2 '("u" "v"))
      (let ((n (bitlength p)))
        (labels ((m (i j)
                   (mk-and (funcall x i)
                           (funcall y j))))
          (mk-not
           (mk-and
            (multiplier #'m u v out (1- n))
            (congruent-to out p (max n (- (* 2 n) 2))))))))))

;;; ------------------------------------------------------------
;;; Sanity checks you can run
;;; ------------------------------------------------------------

;; These should return T once the grader file is loaded.
;;
;; (p-formulap (mk-adder-test 3 2))
;; (p-formulap (p-simplify (mk-adder-test 3 2)))
;; (p-formulap (prime 7))

;; Example equivalence-style use with the grader:
;;
;; (let ((f (mk-adder-test 3 2)))
;;   (assert (p-formulap f))
;;   (tseitin f))


