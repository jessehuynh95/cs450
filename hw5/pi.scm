;;; file: pi.scm
;;;
;;; This should be your second part of HW5.  All
;;; these definitions are from the textbook except cons-stream.

;;; cons-stream is defined (by a macro, as a special form). 

(define-syntax cons-stream
  (syntax-rules ()
    ((_ a b) (cons a (delay b)))))

(define stream-car car)
(define (stream-cdr stream) (force (cdr stream)))
(define stream-null? null?)
(define the-empty-stream '())

(define (stream-foreach f x)
  (if (stream-null? x)
      'done
      (begin (f (stream-car x))
             (stream-foreach f (stream-cdr x)))))

(define (stream-filter pred stream)
  (cond ((stream-null? stream) the-empty-stream)
        ((pred (stream-car stream))
         (cons-stream (stream-car stream)
                      (stream-filter pred (stream-cdr stream))))
        (else (stream-filter pred (stream-cdr stream)))))



;;Problem 1, mult stream
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


;;provides pow for us based on the length of a stream (in our case, a-list)
(define (getpow strm) (expt 10 (- (length strm) 1)))

;;converts a number to a list
(define (num->lst num)
  (let ((lst (string->list (number->string num))))
    (map (lambda (x) (- x (char->integer #\0))) (map char->integer lst))))

(define (list-to-stream lst)
(if (null? lst)
      '()
      (cons-stream (car lst) (list-to-stream (cdr lst)))))

;;if a-list has a shorter length than the previous a-list, add a zero to the front. 
(define (addzero alist1 alist2)
(if (< alist2 0)
        alist1
        (cons 0 (addzero alist1 (- alist2 1))))
    )


;;mult stream function. contains action, consume, and produce functions based on pseudo from pi.pdf
(define (mult-stream m strm)
  ;;checking if the stream is a list or not. if it is, set it to a stream. I was unable to get this to work without set.
  (if (list? strm) (set! strm (list-to-stream strm)))
  ;;action function which dictates if we produce or consume
  (define (action a a-list strm)
    ;;null stream returns remaining a-list elements    
    (cond ((stream-null? strm) (list-to-stream a-list))
          ;;if (m + (a%pow)) < pow) -> produce
          ((and (not (null? a-list)) (< (+ m (remainder a (getpow a-list))) (getpow a-list)))
           (cons-stream
            (car a-list)
            (action (remainder a (if (> (getpow a-list) 1) (getpow a-list) 1)) (cdr a-list) strm)))
          ;;else consume
          (else
           (let ((a2 (+ (* a 10) (* m (stream-car strm)))))
                 (let ((alist2 (num->lst a2)))
                   (action a2 (addzero alist2 (- (length a-list) (length alist2))) (stream-cdr strm)))))))
   (action 0 '() strm)
  )




;;problem 2, pi
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;Procedure to make a matrix
(define (makemtrx A B C D) (list A B C D))

;;procedures to select the specific elements of a matrix
;; | A  B |
;; | C  D |

(define (getA mtrx) (car mtrx))
(define (getB mtrx) (cadr mtrx))
(define (getC mtrx) (caddr mtrx))
(define (getD mtrx) (cadddr mtrx))

;;procedure to add two matrices together
(define (addmtrx mat1 mat2)
  (list
   (+ (getA mat1) (getA mat2))
   (+ (getB mat1) (getB mat2))
   (+ (getC mat1) (getC mat2))
   (+ (getD mat1) (getD mat2))))

;;compose procedure to multiply matrices
(define (compose mat1 mat2)
  (list
   ;;A
   (+ (* (getA mat1) (getA mat2)) (* (getB mat1) (getC mat2)))
   ;;B
   (+ (* (getA mat1) (getB mat2)) (* (getB mat1) (getD mat2)))
   ;;C
   (+ (* (getC mat1) (getA mat2)) (* (getD mat1) (getC mat2)))
   ;;D
   (+ (* (getC mat1) (getB mat2)) (* (getD mat1) (getD mat2)))))


;;Procedure suggested in the document to produce the original input stream
(define (addmtrx-stream mat1 mat2)
  (stream-map addmtrx mat1 mat2))

;;procedure to get the floor
(define (floormtrx mtrx x)
  (let ((a (+ (* (getA mtrx) x) (getB mtrx)))
        (b (getD mtrx)))
    (quotient a b)))

;;shift the matrix 
(define (mtrxshift x)
  (makemtrx 10 (* -10 x) 0 1))

;;First element
(define in1 (makemtrx 1 6 0 3))


(define in2 (makemtrx 1 4 0 2))

;;makes the input stream
(define (strmlintrans 1st)
  (cons-stream 1st (strmlintrans (addmtrx 1st in2))))


;;pi procedure 
(define (pi)
  ;;produce procedure that takes a matrix and a stream as input. computers
  ;;the first elements of the strm until we find a product transformation that
  ;;maps 3 and 4 into numbers that have the same floor
  (define (produce mtrx strm)
    (if (equal?  (floormtrx mtrx 3)  (floormtrx mtrx 4))
      (list (floormtrx mtrx 3) (compose (mtrxshift (floormtrx mtrx 3)) mtrx) strm)
      (produce (compose mtrx (stream-car (stream-cdr strm))) (stream-cdr strm))))

  ;;procedure creates the stream of pi digits
    (define (pistrm firstin)
      (cons-stream (car firstin)
                   (pistrm (produce (cadr firstin)
                           (caddr firstin)))))
  ;;procedure call to return the pi stream
  (pistrm (produce in1 (strmlintrans in1))))










  
  


