(defun halfsum (x y)
    `(Iff ,x (Not ,y)))

(defun halfcarry (x y)
    `(And ,x ,y))

(defun ha (x y s c)
    `(And (Iff ,s (halfsum ,x ,y)) (Iff ,c (halfcarry ,x ,y))))

(defun carry (x y z)
    `(Or (And ,x ,y) (And (Or ,x ,y) ,z)))

(defun sum (x y z)
    (halfsum (halfsum x y) z))

(defun fa (x y z s c)
    (And (Iff s (sum x y z)) (Iff c (carry x y z))))

(defun end-itlist (f l)
    (cond 
        ((null l) (error "end_itlist"))
        ((null (cdr l)) (car l))
        (t (funcall f  (car l) (end-itlist f (cdr l))))))

(defun list_conj (l)
    (if (null l) True (end_itlist mk_and l)))

(defun mk_and (p q)
    `(And ,p ,q))

(defun conjoin (f l)
    (list_conj (mapcar #'f l)))

(defun ripplecarry (x y c out n)
    (conjoin #'(lambda (i) (x i) (y i) (c i) (out i) (c (+ i 1)))) (loop for n from 0 below 5 collect n))

(defun mk-index (x i)
    (intern (format nil "P9~A_~A" x i)))

(defun mk-index (x i j)
    (intern (format nil "P9~A_~A_~A" x i j)))

(defun psimplify1 (fm)
    (match fm
        ((Not False) True)
        ((Not True) False)
        ((Not (Not p)) p)
        ((or (And p False) (And False p)) False)
        ((or (And p True) (And True p)) True)
        ((or (Or p False) (Or False p)) p)
        ((or (Or p True) (Or True p)) p)
        ((or (Imp False p) (Imp p True)) True)
        ((Imp True p) p)
        ((Imp p False) (Not p))
        ((or (Iff p True) (Iff True p)) p)
        ((or (Iff p False) (Iff False p)) (Not p))
        (_ fm)
        ))

(defun psimplify (fm)
    (match fm with
        ((Not p) (psimplify1 (Not(psimplify p))))
        ((And p q) (psimplify1 (And (psimplify p) (psimplify q))))
        ((Or p q) (psimplify1 (Or (psimplify p) (psimplify q))))
        ((Imp p q) (psimplify1 (Imp (psimplify p) (psimplify q))))
        ((Iff p q) (psimplify1 (Iff (psimplify p) (psimplify q))))
        (_ fm)
        ))

(defun ripplecarry0 (x y c out n)
    (psimplify (ripplecarry x y #'(lambda (i) (if (equal i 0) False (c i)) out n))))

(defun ripplecarry1 (x y c out n)
    (psimplify (ripplecarry x y #'(lambda (i) (if (equal i 0) True (c i)) out n))))

(defun mux (sel in0 in1)
    `(Or (And (Not ,sel) ,in0) (And ,sel ,in1)))

(defun offset (n x i)
    (x (+ n i)))

(defun carryselect (x y c0 c1 s0 s1 c s n k)
    (let+ ((k' (min n k))
           (fm `(And (And (ripplecarry0 x y c0 s0 k') (ripplecarry1 x y c1 s1 k'))
                     (And (Iff (c k') (mux (c 0) (c0 k') (c1 k')))
                          (conjoin #'(lambda (i) (Iff (s i) (mux (c 0) (s0 i) (s1 i))))
                                    (loop for each from 0 below k' collect each))))))
        (if (< k' k) fm (And fm (carryselect (offset k x) (offset k y) (offset k c0) (offset k c1)
                                             (offset k s0) (offset k s1) (offset k c) (offset k s)
                                             (- n k) k)))))

(defun mk_adder_test (n k)
    (destructuring-bind (x y c s c0 s0 c1 s1 c2 s2)
        (mapcar #'mk-index '("x" "y" "c" "s" "c0" "s0" "c1" "s1" "c2" "s2"))
    
    (Imp
        (And
            (And (carryselect x y c0 c1 s0 s1 c s n k)
                  (Not (funcall c 0)))
                (ripplecarry0 x y c2 s2 n))
            (And
                (Iff (funcall c n) (funcall c2 n))
                (conjoin (lambda (i) (Iff (funcall s i) (funcall s2 i)))
                                (loop for each from 0 below n collect each))))))

(defun rippleshift (u v c z w n)
    (ripplecarry0 u v (lambda (i) (if (equal i n) (w (- n 1)) (c (+ i 1))))
                      (lambda (i) (if (equal i 0) z (w (- i 1))))
                      n))

(defun multiplier (x u v out n)
    (if (equal n 1) (Add (Iff (out 0) (x 0 0)) (Not (out 1)))
                    (psimplify (And (Iff (out 0) (x 0 0))
                                    (And (rippleshift
                                            (lambda (i) (if (equal i (- n 1)) False (x 0 (+ i 1))))
                                            (x 1) (v 2) (out 1) (u 2) n)
                                        (if (equal n 2) (Add (Iff (out 2) (u 2 0)) (Iff (out 3) (u 2 1)))
                                            (conjoin (lambda (k) (rippleshift (u k) (x k) (v (+ 1 k)) (out k)
                                            (if (equal k (- n 1)) (lambda (i) (out (+ n i))) (u (+ k 1)))
                                            n)
                                            (loop for each from 2 below n collect each)))))))))

(defun bitlength (x)
    (if (equal x 0) 0 (+ 1 (bitlength (/ x 2)))))

(defun bit (n x)
    (if (equal n 0) (equal 1 (mod x 2)) (bit (- n 1) (/ x 2))))

(defun congruent_to (x m n)
    (conjoin (lambda (i) (if (bit i m) (x i) (Not x i)))
             (loop for each from 0 below n collect each)))

(defun prime (p)
    (destructuring-bind (x y out)
        (mapcar #'mk-index '("x" "y" "out"))
    (destructuring-bind (u v)
        (mapcar #'mk-index2 '("u" "v"))
            (let ((n (bitlength p)))
                (labels ((m (i j)
                            (And (funcall x i)
                                 (funcall y j))))
                   (Not
                    (And (multiplier #'m u v out (1- n))
                         (congruent_to out p (max n (- (* 2 n) 2))))))))))

