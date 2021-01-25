;; HW4 - part 1 and optimal BST

;;; Answer part 1 here.


;Question 1a
;I simply added lambdas for all the variables.
(define make-account-lambda
         (lambda (balance)
           (define withdraw
             (lambda (amount)
               (if (>= balance amount)
                   (begin (set! balance (- balance amount))
                          balance)
                   "Insufficient funds")))
           (define deposit
             (lambda (amount)
               (set! balance (+ balance amount))
               balance))
           (lambda (m)  
             (cond ((eq? m 'withdraw) withdraw)
                   ((eq? m 'deposit) deposit)
                   (else (error "Unknown request --> MAKE-ACCOUNT" m))))))


;question 1b
;Took the withdraw and deposit procedures and moved them into the cond statement.
(define make-account-inline
         (lambda (balance)
           (lambda (m)  
             (cond ((eq? m 'withdraw) (lambda (amount)
               (if (>= balance amount)
                   (begin (set! balance (- balance amount))
                          balance)
                   "Insufficient funds")))
                   ((eq? m 'deposit) (lambda (amount)
               (set! balance (+ balance amount))
               balance))
                   (else (error "Unknown request --> MAKE-ACCOUNT" m))))))


;question 1c
;"factored" out the lambda(amount) from the cond statement so it only needs to be called once.
(define make-account-inline-factored
         (lambda (balance)
           (lambda (m)
             (lambda (amount)
             (cond ((eq? m 'withdraw) 
               (if (>= balance amount)
                   (begin (set! balance (- balance amount))
                          balance)
                   "Insufficient funds"))
                   ((eq? m 'deposit) 
               (set! balance (+ balance amount))
               balance)
                   (else (error "Unknown request --> MAKE-ACCOUNT" m)))))))



;question 3, Exercise 3.2

(define (make-monitored f)
  ;starts the number of calls at 0
  (let ((calls 0))
    (lambda (mf)
      ;first cond: special symbol to return call value
      (cond ((equal? mf 'how-many-calls?) calls)
            ;second cond resets call value to zero
            ((equal? mf 'reset-count) (set! calls 0))
            ;else increments calls by 1
            (else (begin (set! calls (+ calls 1)) 
                          (f mf)))
			))))	



;question 4, Exercise 3.3
;for some reason, without this output function I was getting a lot of errors that said 'application: not a procedure;\n expected a procedure that can be applied to arguments\'.
;I added it in so that it would have a function and return something, which seems to have worked.
(define make-pw-account
  (lambda (bal saved)
    (let ((pwacc (make-account-inline-factored bal)))
    (define (output input m)
      (lambda (amt)
        (cond ((eq? input saved)
               ((pwacc m) amt))
              (else "Incorrect password"))))
      output)))

;; Part 2 starts here! 
;; read-file produces a list whose elements are the expressions in the file.
  (define (read-file)
    (let ((expr (read)))
      (if (eof-object? expr)
          '()
          (cons expr (read-file)))))

;(define data (list (list 10 34) (list 12 8) (list 20 50)))
 ; (define data (with-input-from-file "keys.dat" read-file))

 (define (entry tree) (car tree))
 (define (key entry) (car entry))
 (define (freq entry) (cadr entry))
 (define (left-branch tree) (cadr tree)) 
 (define (right-branch tree) (caddr tree)) 


 (define (make-tree entry left right) 
   (list entry left right)) 
  
 (define (adjoin-set x set) 
   (cond ((null? set) (make-tree x '() '()))
         (else
          (let ((rkey (car (entry set))))
            (cond ((= (car x) rkey) set) 
                  ((< (car x) rkey)
                   (make-tree (entry set) 
                              (adjoin-set x (left-branch set)) 
                              (right-branch set))) 
                  ((> (car x) rkey) 
                   (make-tree (entry set) 
                              (left-branch set) 
                              (adjoin-set x (right-branch set))))))))) 
 ;; A skeleton for BST. You may add things here 
 (define (make-table) 
   (let ((local-table '())) 
      
     (define (lookup key records) 
       (if (null? records) #f
           (let ((rkey (car (entry records))))
             (cond ((= key rkey) (entry records)) 
                   ((< key rkey) (lookup key (left-branch records))) 
                   ((> key rkey) (lookup key (right-branch records))))))) 
      
     (define (insert! dat)
       (let ((rkey (car dat)))
         (let ((record (lookup rkey local-table))) 
           (if record 
               (set-cdr! record (freq dat)) 
               (set! local-table (adjoin-set dat local-table)))))) 
      
     (define (get key) 
       (lookup key local-table))
     
     ;build table from data. Data is a list of (key freq)
     (define (build-tree-from-data the-keys)
       (if (null? the-keys) 'ok
        (begin (insert! (car the-keys))
             (build-tree-from-data (cdr the-keys)))))
     
     (define (dispatch m) 
       (cond ((eq? m 'get-proc) get) 
             ((eq? m 'insert-proc) insert!)
             ((eq? m 'build-proc) build-tree-from-data)
             ((eq? m 'print) local-table) 
             (else  "Undefined operation -- TABLE" m))) 
     dispatch)) 
  
 (define table (make-table)) 
 (define get (table 'get-proc)) 
 (define put (table 'insert-proc))
 (define cost (table 'cost-proc))

;;; Put your naive and DP procedures here.

;function that returns the list to the left of the key
(define (lsplit lst key)
    (cond ((null? lst) '())
          ((< (caar lst) key)
                 (cons (car lst) (lsplit (cdr lst) key)))
          (else (lsplit (cdr lst) key))))

;function that returns the list to the right
(define (rsplit lst key)
    (cond ((null? lst) '())
          ((> (caar lst) key)
                 (cons (car lst) (rsplit (cdr lst) key)))
          (else (rsplit (cdr lst) key))))

;function to get the sum of the weights
(define (wsum lst)
  (cond ((null? lst) 0)
        ((null? (cdr lst)) (car (cdar lst)))
        (else (+ (car (cdar lst)) (wsum (cdr lst))))))


(define (listkey list)
  (caar list))


(define (naive-call lst lstcopy)
(let ((listiter lst))
    (let ((minim2 1000000))
      (define weight 0)
      (let loop ((ls lst) (lt listiter))
      ;(define lweight (min-cost-naive (lsplit lst (listkey lstcopy))))
      ;(define rweight (min-cost-naive (rsplit lst (listkey lstcopy))))
      ;recursive loop through the tree
      (cond ((null? lst) (begin (set! weight 0)))
            ((null? (cdr lst)) (begin (set! weight (car (cdar lst)))))
            (else (set! weight (+ (wsum lst) (min-cost-naive (lsplit lst (listkey listiter))) (min-cost-naive (rsplit lst (listkey listiter)))))))
      (if (< weight minim2)
          (begin (set! minim2 weight)))


        (set! listiter (cdr listiter))

      (if (not (null?  listiter))
           (loop lst listiter)))
        
    minim2)))

(define (min-cost-naive lst)
  (define lstcopy lst)
    (cond ((null? lst) 0)
          (else (naive-call lst lstcopy))))


;;;; the following procedure is handy for timing things
(#%require (only racket/base current-milliseconds))
(define (runtime) (current-milliseconds))

(define (timed f . args)
  (let ((init (runtime)))
    (let ((v (apply f args)))
      (display (list 'time: (- (runtime) init)))
      (newline)
      v)))