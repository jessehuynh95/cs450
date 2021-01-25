(#%require (only racket/base error))
;;; file: s450.scm
;;;
;;; Metacircular evaluator from chapter 4 of STRUCTURE AND
;;; INTERPRETATION OF COMPUTER PROGRAMS (2nd edition)
;;;
;;; Modified by kwn, 3/4/97
;;; Modified and commented by Carl Offner, 10/21/98 -- 10/12/04
;;;
;;; This code is the code for the metacircular evaluator as it appears
;;; in the textbook in sections 4.1.1-4.1.4, with the following
;;; changes:
;;;
;;; 1.  It uses #f and #t, not false and true, to be Scheme-conformant.
;;;
;;; 2.  Some function names were changed to avoid conflict with the
;;; underlying Scheme:
;;;
;;;       eval => xeval
;;;       apply => xapply
;;;       extend-environment => xtend-environment
;;;
;;; 3.  The driver-loop is called s450.
;;;
;;; 4.  The booleans (#t and #f) are classified as self-evaluating.
;;;
;;; 5.  These modifications make it look more like UMB Scheme:
;;;
;;;        The define special form evaluates to (i.e., "returns") the
;;;          variable being defined.
;;;        No prefix is printed before an output value.
;;;
;;; 6.  I changed "compound-procedure" to "user-defined-procedure".
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;;	 xeval and xapply -- the kernel of the metacircular evaluator
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (xeval exprs env)
  (let ((action (lookup-action (type-of exprs))))
    (if action (action exprs env)
        (cond ((self-evaluating? exprs) exprs)
              ((variable? exprs)
	       (if (lookup-action exprs)
                   (begin (display "Special form: ") (display exprs) (newline))
                   (lookup-variable-value exprs env)))
              ((thunk? exprs) (list 'thunk (thunkexpr exprs)))
              ;;; added a condition to check if it is a primitive procedure or delayed
	      ((application? exprs)
               (let ((proced (xeval (car exprs) env)))
                 (xapply proced
                         (if (primitive-procedure? proced)
                             (list-of-values (cdr exprs) env)
                             (list-of-values-delayed (cadr proced) (cdr exprs) env)))))
	      (else
	       (error "Unknown expression type -- XEVAL " exprs)))))
  )



;;; original xeval body  
;  (cond ((self-evaluating? exp) exp)
;       ((variable? exp) (lookup-variable-value exp env))
;       ((quoted? exp) (text-of-quotation exp))
;       ((assignment? exp) (eval-assignment exp env))
;       ((definition? exp) (eval-definition exp env))
;       ((if? exp) (eval-if exp env))
;       ((lambda? exp)
;       (make-procedure (lambda-parameters exp)
;                       (lambda-body exp)
;                         env))
;       ((begin? exp) 
;        (eval-sequence (begin-actions exp) env))
;       ((cond? exp) (xeval (cond->if exp) env))
;       ((application? exp)
;        (xapply (xeval (operator exp) env)
;		 (list-of-values (operands exp) env)))
;       (else
;         (error "Unknown expression type -- XEVAL " exp))))

(define (xapply procedure arguments)
  (cond ((primitive-procedure? procedure)
         (apply-primitive-procedure procedure arguments))
        ((user-defined-procedure? procedure)
         (eval-sequence
           (procedure-body procedure)
           (xtend-environment
             (procedure-parameters procedure)
             arguments
             (procedure-environment procedure))))
        (else
         (error
          "Unknown procedure type -- XAPPLY " procedure))))

;;; Handling procedure arguments

(define (list-of-values exps env)
  (if (no-operands? exps)
      '()
      (cons (xeval (first-operand exps) env)
            (list-of-values (rest-operands exps) env))))


;;; handling evaluations if formal argument is delayed
(define (list-of-values-delayed param exprs env)
  (if (no-operands? exprs)
      '()
      (cons
       (let ((param2 (car param))
             (operand (car exprs)))
         (cond ((delayed? param2) (thunkify operand env))
               (else (xeval operand env)))
         )
       (list-of-values-delayed
        (cdr param) (cdr exprs) env))))

;;; These functions, called from xeval, do the work of evaluating some
;;; of the special forms:

(define (eval-if exp env)
  (if (true? (xeval (if-predicate exp) env))
      (xeval (if-consequent exp) env)
      (xeval (if-alternative exp) env)))

(define (eval-sequence exps env)
  (cond ((last-exp? exps) (xeval (first-exp exps) env))
        (else (xeval (first-exp exps) env)
              (eval-sequence (rest-exps exps) env))))

(define (eval-assignment exp env)
  (let ((name (assignment-variable exp)))
    (set-variable-value! name
			 (xeval (assignment-value exp) env)
			 env)
  name))    ;; A & S return 'ok

(define (eval-definition exp env)
  (let ((name (definition-variable exp)))  
    (define-variable! name
      (xeval (definition-value exp) env)
      env)
  name))     ;; A & S return 'ok

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;;	lookup-action and type-of for problem 2. Including 
;;;     Including install-special-form here as well.
;;; 
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


;;; install-special-form is used to install new special forms into
;;; a table that lists all special forms.

;;;our special forms table starts out as an empty list
(define specform-table (list '()))

;;;lookup-action which checks to see if the action is in the special forms table
(define (lookup-action action)
  (let ((entry (assoc action (cdr specform-table))))
    (if entry (cdr entry)
        #f)))

;;; type-of returns what special form an expression represents. If nothing, null.
(define (type-of exprs)
  (if (list? exprs) (car exprs)
      '()))


;;; procedure to check if a something is already defined.

(define (defined? input env)
  (define (looper env)
    (define (checker in1 value)
      (cond ((null? in1) (looper (enclosing-environment env)))
            ((equal? input (car in1)) #t)
            (else (checker (cdr in1) (cdr value)))))
    (if (equal? env '())
        #f
        (let ((frm (car env)))
          (checker (car frm) (cdr frm)))))
  (looper env))

;;; procedure to add special forms to the specform table and returns the
;;; name of the special form being installed
(define (installsf key val tab)
  (let ((entry (assoc key (cdr tab))))
    (if entry (set-cdr! entry val)
        (set-cdr! tab (cons (cons key val) (cdr tab))))) key)


;;; The install-special-forms procedure which takes a special form as
;;; a quoted tag and a lambda expression and inserts them onto a table
;;; if they are not already there as a key value pair.
(define (install-special-form specform body)
  (cond ((defined? specform the-global-environment)
         (error "giving a defined name to a new special form: " specform))
        ((not (equal? #f
                      (let ((entry (assoc specform (cdr specform-table))))
                        (if entry (cdr entry) #f))))
         (error "reinstalling a special form: " specform))
        (else (installsf specform body specform-table))))






;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;;	 Representing expressions
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; Numbers, strings, and booleans are all represented as themselves.
;;; (Not characters though; they don't seem to work out as well
;;; because of an interaction with read and display.)

(define (self-evaluating? exp)
  (or (number? exp)
      (string? exp)
      (boolean? exp)
      ))

;;; variables -- represented as symbols

(define (variable? exp) (symbol? exp))

;;; quote -- represented as (quote <text-of-quotation>)

(define (quoted? exp)
  (tagged-list? exp 'quote))

(define (text-of-quotation exp) (cadr exp))

(define (tagged-list? exp tag)
  (if (pair? exp)
      (eq? (car exp) tag)
      #f))

;;; assignment -- represented as (set! <var> <value>)

(define (assignment? exp) 
  (tagged-list? exp 'set!))

(define (assignment-variable exp) (cadr exp))

(define (assignment-value exp) (caddr exp))

;;; definitions -- represented as
;;;    (define <var> <value>)
;;;  or
;;;    (define (<var> <parameter_1> <parameter_2> ... <parameter_n>) <body>)
;;;
;;; The second form is immediately turned into the equivalent lambda
;;; expression.

(define (definition? exp)
  (tagged-list? exp 'define))

(define (definition-variable exp)
  (if (symbol? (cadr exp))
      (cadr exp)
      (caadr exp)))

(define (definition-value exp)
  (if (symbol? (cadr exp))
      (caddr exp)
      (make-lambda (cdadr exp)
                   (cddr exp))))

;;; lambda expressions -- represented as (lambda ...)
;;;
;;; That is, any list starting with lambda.  The list must have at
;;; least one other element, or an error will be generated.

(define (lambda? exp) (tagged-list? exp 'lambda))

(define (lambda-parameters exp) (cadr exp))
(define (lambda-body exp) (cddr exp))

(define (make-lambda parameters body)
  (cons 'lambda (cons parameters body)))

;;; conditionals -- (if <predicate> <consequent> <alternative>?)

(define (if? exp) (tagged-list? exp 'if))

(define (if-predicate exp) (cadr exp))

(define (if-consequent exp) (caddr exp))

(define (if-alternative exp)
  (if (not (null? (cdddr exp)))
      (cadddr exp)
      #f))

(define (make-if predicate consequent alternative)
  (list 'if predicate consequent alternative))


;;; sequences -- (begin <list of expressions>)

(define (begin? exp) (tagged-list? exp 'begin))

(define (begin-actions exp) (cdr exp))

(define (last-exp? seq) (null? (cdr seq)))
(define (first-exp seq) (car seq))
(define (rest-exps seq) (cdr seq))

(define (sequence->exp seq)
  (cond ((null? seq) seq)
        ((last-exp? seq) (first-exp seq))
        (else (make-begin seq))))

(define (make-begin seq) (cons 'begin seq))


;;; procedure applications -- any compound expression that is not one
;;; of the above expression types.

(define (application? exp) (pair? exp))
(define (operator exp) (car exp))
(define (operands exp) (cdr exp))

(define (no-operands? ops) (null? ops))
(define (first-operand ops) (car ops))
(define (rest-operands ops) (cdr ops))


;;; Derived expressions -- the only one we include initially is cond,
;;; which is a special form that is syntactically transformed into a
;;; nest of if expressions.

(define (cond? exp) (tagged-list? exp 'cond))

(define (cond-clauses exp) (cdr exp))

(define (cond-else-clause? clause)
  (eq? (cond-predicate clause) 'else))

(define (cond-predicate clause) (car clause))

(define (cond-actions clause) (cdr clause))

(define (cond->if exp)
  (expand-clauses (cond-clauses exp)))

(define (expand-clauses clauses)
  (if (null? clauses)
      #f                          ; no else clause -- return #f
      (let ((first (car clauses))
            (rest (cdr clauses)))
        (if (cond-else-clause? first)
            (if (null? rest)
                (sequence->exp (cond-actions first))
                (error "ELSE clause isn't last -- COND->IF "
                       clauses))
            (make-if (cond-predicate first)
                     (sequence->exp (cond-actions first))
                     (expand-clauses rest))))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;;	 Homework 7-1: Delayed expressions
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; returns if the argument is tagged as a delayed argument
(define (delayed? expr)
  (tagged-list? expr 'delayed))

;;; returns the variable of a delayed argument
(define (del-var expr)
  (car (cdr expr)))

;;; creates a thunk object that is a list labeled as a thunk containing
;;; an expression and the current environment
(define (thunkify expr env)
  (list 'thunk expr env))

;;; returns if something is a thunk or not by seeing if the first element
;;; in the list is the 'thunk label
(define (thunk? expr)
  (tagged-list? expr 'thunk))

;;; returns the expression and environment from the thunk by pulling the
;;; corresponding elements of the list
(define (thunkenv env)
  (car (cdr (cdr env))))
(define (thunkexpr expr)
  (car (cdr expr)))

;;; force the evaluation of the thunk
(define (thunkeval thunk)
  (xeval (thunkexpr thunk) (thunkenv thunk)))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;;	 Homework 7-1: streams
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;



;;; defining primitive procedures ahead of time to call later
(define (stream-car stream)
  (car stream))
(define (stream-cdr stream)
  (thunkeval (cdr stream)))
(define (stream-null? stream)
  (eqv? stream the-empty-stream))
(define the-empty-stream '())


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;;	 Truth values and procedure objects
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; Truth values

(define (true? x)
  (not (eq? x #f)))

(define (false? x)
  (eq? x #f))


;;; Procedures

(define (make-procedure parameters body env)
  (list 'procedure parameters body env))

(define (user-defined-procedure? p)
  (tagged-list? p 'procedure))


(define (procedure-parameters p) (cadr p))
(define (procedure-body p) (caddr p))
(define (procedure-environment p) (cadddr p))


;;; untags tagged parameters
(define (procedure-untag p)
  (define (tagremove param)
    (if (null? param) '()
        (cons
         (let ((param2 (car param)))
           (cond ((delayed? param2) (del-var param2))
                 (else param2))
           )
         (tagremove (cdr param)))
        )
    )       
  (tagremove (procedure-parameters p)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;;	 Representing environments
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; An environment is a list of frames.

(define (enclosing-environment env) (cdr env))

(define (first-frame env) (car env))

(define the-empty-environment '())

;;; Each frame is represented as a pair of lists:
;;;   1.  a list of the variables bound in that frame, and
;;;   2.  a list of the associated values.

(define (make-frame variables values)
  (cons variables values))

(define (frame-variables frame) (car frame))
(define (frame-values frame) (cdr frame))

(define (add-binding-to-frame! var val frame)
  (set-car! frame (cons var (car frame)))
  (set-cdr! frame (cons val (cdr frame))))

;;; Extending an environment

(define (xtend-environment vars vals base-env)
  (if (= (length vars) (length vals))
      (cons (make-frame vars vals) base-env)
      (if (< (length vars) (length vals))
          (error "Too many arguments supplied " vars vals)
          (error "Too few arguments supplied " vars vals))))

;;; Looking up a variable in an environment

(define (lookup-variable-value var env)
  (define (env-loop env)
    (define (scan vars vals)
      (cond ((null? vars)
             (env-loop (enclosing-environment env)))
            ((eq? var (car vars))
             (let ((val (car vals)))
               (cond ((thunk? val) (thunkeval val))
                     (else val))))
            (else (scan (cdr vars) (cdr vals)))))
    (if (eq? env the-empty-environment)
        (error "Unbound variable " var)
        (let ((frame (first-frame env)))
          (scan (frame-variables frame)
                (frame-values frame)))))
  (env-loop env))

;;; Setting a variable to a new value in a specified environment.
;;; Note that it is an error if the variable is not already present
;;; (i.e., previously defined) in that environment.

(define (set-variable-value! var val env)
  (define (env-loop env)
    (define (scan vars vals)
      (cond ((null? vars)
             (env-loop (enclosing-environment env)))
            ((eq? var (car vars))
             (set-car! vals val))
            (else (scan (cdr vars) (cdr vals)))))
    (if (eq? env the-empty-environment)
        (error "Unbound variable -- SET! " var)
        (let ((frame (first-frame env)))
          (scan (frame-variables frame)
                (frame-values frame)))))
  (if (lookup-action var) (error "defining a special form name:" var)
  (env-loop env)))

;;; Defining a (possibly new) variable.  First see if the variable
;;; already exists.  If it does, just change its value to the new
;;; value.  If it does not, define the new variable in the current
;;; frame.

(define (define-variable! var val env)
  (if (lookup-action var) (error "defining a special form name: " var)
      (let ((frame (first-frame env)))
        (define (scan vars vals)
          (cond ((null? vars)
                 (add-binding-to-frame! var val frame))
                ((eq? var (car vars))
                 (set-car! vals val))
                (else (scan (cdr vars) (cdr vals)))))
        (scan (frame-variables frame)
              (frame-values frame)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;;	 The initial environment
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; This is initialization code that is executed once, when the the
;;; interpreter is invoked.

(define (setup-environment)
  (let ((initial-env
         (xtend-environment '()
                            '()
                            the-empty-environment)))
    initial-env))

;;; Define the primitive procedures

(define (primitive-procedure? proc)
  (tagged-list? proc 'primitive))

(define (primitive-implementation proc) (cadr proc))

;;; Commenting out original primitive procedures.

;(define primitive-procedures
;  (list (list 'car car)
;        (list 'cdr cdr)
;        (list 'cons cons)
;        (list 'null? null?)
;;      more primitives
;        ))

;(define (primitive-procedure-names)
;  (map car
;       primitive-procedures))

;(define (primitive-procedure-objects)
;  (map (lambda (proc) (list 'primitive (cadr proc)))
;       primitive-procedures))

;;; Here is where we rely on the underlying Scheme implementation to
;;; know how to apply a primitive procedure.

(define (apply-primitive-procedure proc args)
  (apply (primitive-implementation proc) args))


;;; install-primitive-procedure which inserts a procedure into the
;;; procedure table similar to install-special-form based on the
;;; homework handout.

(define (install-primitive-procedure name action)
  (if (lookup-action name)
      (error "installing a primitive procedure with the name of a special form: " name)
      (define-variable! name (list 'primitive action) the-global-environment))
  name)


;(define (exit)
;  (display "Exiting s450...")
;  '() )

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;;	 The main driver loop
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; Note that (read) returns an internal representation of the next
;;; Scheme expression from the input stream.  It does NOT evaluate
;;; what is typed in -- it just parses it and returns an internal
;;; representation.  It is the job of the scheme evaluator to perform
;;; the evaluation.  In this case, our evaluator is called xeval.

(define input-prompt "s450==> ")

(define (s450)
  (prompt-for-input input-prompt)
  (let ((input (read)))
    (let ((output (xeval input the-global-environment)))
      (user-print output)))
  (s450))

(define (prompt-for-input string)
  (newline) (newline) (display string))

;;; Note that we would not want to try to print a representation of the
;;; <procedure-env> below -- this would in general get us into an
;;; infinite loop.

(define (user-print object)
  (if (user-defined-procedure? object)
      (display (list 'user-defined-procedure
                     (procedure-parameters object)
                     (procedure-body object)
                     '<procedure-env>))
      (display object)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;;	 Here we go:  define the global environment and invite the
;;;        user to run the evaluator.
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(define the-global-environment (setup-environment))

;;; Calling install-special-form on special forms before getting into the s450 per pizza post 222


(display "... loaded the metacircular evaluator. (s450) runs it.")
(newline)


;;; installing special forms from xeval
(install-special-form 'quote
                      (lambda (exprs env)
                        (text-of-quotation exprs)))
(install-special-form 'set!
                      (lambda (exprs env)
                        (eval-assignment exprs env)))
(install-special-form 'define
                        (lambda (exprs env)
                          (eval-definition exprs env)))
(install-special-form 'if
                      (lambda (exprs env)
                        (eval-if exprs env)))
(install-special-form 'lambda
                      (lambda (exprs env)
                        (make-procedure (lambda-parameters exprs)
                                        (lambda-body exprs)
                                        env)))
(install-special-form 'begin
                      (lambda (exprs env)
                          (eval-sequence (begin-actions exprs) env)))
(install-special-form 'cond
                      (lambda (exprs env)
                          (xeval (cond->if exprs) env)))
(install-special-form 'load
                      (lambda (exp env)
                        (define (filename exp) (cadr exp))
                        (define thunk (lambda ()
                                        (readfile)
                                        ))
                        (define readfile (lambda()
                                           (let ((item (read)))
                                             (if (not (eof-object? item))
                                                 (begin
                                                   (xeval item env)
                                                   (readfile))))
                                           ))
                        (with-input-from-file (filename exp) thunk)
                        (filename exp)      ; return the name of the file - why not?
                        ))

;;; defined? special form from problem 6
(install-special-form 'defined?
                        (lambda (exprs env)      
                          (defined? (cadr exprs) env)))
(install-special-form 'locally-defined?
                      (lambda (exprs env)                        
                        (cond ((member (car (cdr exprs)) (car (car env)))
                               #t)
                              (else #f)
                              )))
(install-special-form 'make-unbound!
                      (lambda (exprs env)                        
                        (define (looper env)
                          (define (checker var val)
                            (cond ((null? var) (looper (cdr env)))
                                  ((equal? (car (cdr exprs)) (car var))
                                   (set-car! var '()) (looper (cdr env)))
                                  (else (checker (cdr var) (cdr val)))))
                          (if (equal? env '())
                              "unbounded"
                              (let ((frame (car env)))
                                (checker (car frame) (cdr frame)))))
                        (looper env)))
                     
(install-special-form 'locally-make-unbound!
                      (lambda (exprs env)                        
                        (define (looper env)
                          (define (checker var val)
                            (cond ((null? var) "unbounded")
                                  ((equal? (car (cdr exprs)) (car var))
                                   (set-car! var '()) (looper (cdr env)))
                                  (else (checker (cdr var) (cdr val)))))
                          (if (equal? env '())
                              "unbounded"
                              (let ((frame (car env)))
                                (checker (car frame) (cdr frame)))))
                        (looper env)))

;;; installing special form cons-stream hw 7-1

(install-special-form 'cons-stream
                      (lambda (expr env)                        
                        (cons (car (cdr expr)) (thunkify (car (cdr (cdr expr))) env))))


(install-primitive-procedure '+ +)
(install-primitive-procedure '- -)
(install-primitive-procedure '= =)
(install-primitive-procedure '* *)
(install-primitive-procedure '/ /)
(install-primitive-procedure 'newline newline)
(install-primitive-procedure 'equal? equal?)
(install-primitive-procedure 'car car)
(install-primitive-procedure 'cdr cdr)
(install-primitive-procedure 'cons cons)
(install-primitive-procedure 'null? null?)
(install-primitive-procedure 'display display)
;(install-primitive-procedure 'exit exit)

;;;installing primitive procedures for hw7-1
(install-primitive-procedure 'stream-car stream-car)
(install-primitive-procedure 'stream-cdr stream-cdr)
(install-primitive-procedure 'stream-null? stream-null?)
