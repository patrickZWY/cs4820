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

(defun mk_index (x i)
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