;;;; RSA.SCM

;;;; fast modular exponentiation. From the textbook, section 1.2.4

(define (expmod b e m)
  (cond ((zero? e) 1)
        ((even? e)
         (remainder (square (expmod b (/ e 2) m))
                    m))
        (else
         (remainder (* b (expmod b (- e 1) m))
                    m))))

(define (square x) (* x x))


;;; An RSA key consists of a modulus and an exponent.

(define make-key cons)
(define key-modulus car)
(define key-exponent cdr)

(define (RSA-transform number key)
  (expmod number (key-exponent key) (key-modulus key)))

;;; The following routine compresses a list of numbers to a single
;;; number for use in creating digital signatures.

(define (compress intlist)
  (define (add-loop l)
    (if (null? l)
        0
        (+ (car l) (add-loop (cdr l)))))
  (modulo (add-loop intlist) (expt 2 28)))
;;;; generating RSA keys

;;; To choose a prime, we start searching at a random odd number in a
;;; specifed range
(#%require (only racket/base random))
(define (choose-prime smallest range)
  (let ((start (+ smallest (choose-random range))))
    (search-for-prime (if (even? start) (+ start 1) start))))

(define (search-for-prime guess)
  (if (fast-prime? guess 2)
      guess
      (search-for-prime (+ guess 2))))

;;; The following procedure picks a random number in a given range,
;;; but makes sure that the specified range is not too big for
;;; Scheme's RANDOM primitive.

(define choose-random
  ;; restriction of Scheme RANDOM primitive
  (let ((max-random-number (expt 10 25))) 
    (lambda (n)
      (random (inexact->exact(floor (min n max-random-number)))))))


;;; The Fermat test for primality, from the texbook section 1.2.6

(define (fermat-test n)
    (let ((a (choose-random n)))
      (= (expmod a n n) a)))

(define (fast-prime? n times)
    (cond ((zero? times) #t)
          ((fermat-test n) (fast-prime? n (- times 1)))
          (else #f)))
;;; RSA key pairs are pairs of keys

(define make-key-pair cons)
(define key-pair-public car)
(define key-pair-private cdr)

;;; generate an RSA key pair (k1, k2).  This has the property that
;;; transforming by k1 and transforming by k2 are inverse operations.
;;; Thus, we can use one key as the public key andone as the private key.
(define (generate-RSA-key-pair)
  (let ((size (expt 2 20)))
    ;; we choose p and q in the range from 2^14 to 2^15.  This insures
    ;; that the pq will be in the range 2^28 to 2^30, which is large
    ;; enough to encode four characters per number.
    (let ((p (choose-prime size size))
          (q (choose-prime size size)))
    (if (= p q)       ;check that we haven't chosen the same prime twice
        (generate-RSA-key-pair)     ;(VERY unlikely)
        (let ((n (* p q))
              (m (* (- p 1) (- q 1))))
          (let ((e (select-exponent m)))
            (let ((d (invert-modulo e m)))
              (make-key-pair (make-key n e) (make-key n d)))))))))


;;; The RSA exponent can be any random number relatively prime to m

(define (select-exponent m)
  (let ((try (choose-random m)))
    (if (= (gcd try m) 1)
        try
        (select-exponent m))))


;;; Invert e modulo m

(define (invert-modulo e m)
  (if (= (gcd e m) 1)
      (let ((y (cdr (solve-ax+by=1 m e))))
        (modulo y m))                   ;just in case y was negative
      (error "gcd not 1" e m)))


;;; solve ax+by=1
;;; The idea is to let a=bq+r and solve bx+ry=1 recursively

(define (solve-ax+by=1 a b)
    (if (= b 0)
      (cons 1 0)
      (let ((quote (quotient a b))
            (remain (remainder a b)))
        (let ((solveagain (solve-ax+by=1 b remain)))
          (cons (cdr solveagain) (+ (* (cdr solveagain) (- quote)) (car solveagain)))))))
  
;;; Actual RSA encryption and decryption

(define (RSA-encrypt string key1)
  (RSA-convert-list (string->intlist string) key1))


(define (RSA-convert-list intlist key)
  (let ((n (key-modulus key)))
    (define (convert l sum)
      (if (null? l)
          '()
          (let ((x (RSA-transform (modulo (- (car l) sum) n)
                                  key)))
            (cons x (convert (cdr l) x)))))
    (convert intlist 0)))


   (define (RSA-decrypt intlist key2)
     (intlist->string (RSA-unconvert-list intlist key2)))

;;;(define (RSA-unconvert-list intlist key) ...)
;;;  You must complete this procedure 

(define (RSA-unconvert-list intlist key)
  (let ((n (key-modulus key)))
    (define (unconvert l sum)
      (if (null? l)
          '()
        (let ((x (modulo (+ sum
                            (RSA-transform (car l) key))
                         n)))
          (cons x (unconvert (cdr l) (car l))))))
    (unconvert intlist 0)))



;;;; searching for divisors.

;;; The following procedure is very much like the find-divisor
;;; procedure of section 1.2.6 of the test, except that it increments
;;; the test divisor by 2 each time (compare exercise 1.18 of the
;;; text).  You should be careful to call it only with odd numbers n.

(define (smallest-divisor n)
  (find-divisor n 3))

(define (find-divisor n test-divisor)
  (cond ((> (square test-divisor) n) n)
        ((divides? test-divisor n) test-divisor)
        (else (find-divisor n (+ test-divisor 2)))))

(define (divides? a b)
  (= (remainder b a) 0))



;;; crack-rsa
;;; Used to find a private key given a public key.

(define (crack-rsa public-key)
  (let ((n (key-modulus public-key))
        (e (key-exponent public-key)))
  (make-key n (invert-modulo e (* (- (smallest-divisor n) 1) (- (/ n (smallest-divisor n)) 1))))))



;;;; converting between strings and numbers

;;; The following procedures are used to convert between strings, and
;;; lists of integers in the range 0 through 2^28.  You are not
;;; responsible for studying this code -- just use it.

;;; Convert a string into a list of integers, where each integer
;;; encodes a block of characters.  Pad the string with spaces if the
;;; length of the string is not a multiple of the blocksize.

(define (string->intlist string)
  (let ((blocksize 4))
    (let ((padded-string (pad-string string blocksize)))
      (let ((length (string-length padded-string)))
        (block-convert padded-string 0 length blocksize)))))

(define (block-convert string start-index end-index blocksize)
  (if (= start-index end-index)
      '()
      (let ((block-end (+ start-index blocksize)))
        (cons (charlist->integer
	       (string->list (substring string start-index block-end)))
              (block-convert string block-end end-index blocksize)))))

(define (pad-string string blocksize)
  (let ((rem (remainder (string-length string) blocksize)))
    (if (= rem 0)
        string
        (string-append string (make-string (- blocksize rem) #\Space)))))

;;; Encode a list of characters as a single number
;;; Each character gets converted to an ascii code between 0 and 127.
;;; Then the resulting number is c[0]+c[1]*128+c[2]*128^2,...

(define (charlist->integer charlist)
  (let ((n (char->integer (car charlist))))
    (if (null? (cdr charlist))
        n
        (+ n (* 128 (charlist->integer (cdr charlist)))))))

;;; Convert a list of integers to a string. (Inverse of
;;; string->intlist, except for the padding.)

(define (intlist->string intlist)
  (list->string
   (apply
    append
    (map integer->charlist intlist))))
;;; Decode an integer into a list of characters.  (This is essentially
;;; writing the integer in base 128, and converting each "digit" to a
;;; character.)


(define (integer->charlist integer)
  (if (< integer 128)
      (list (integer->char integer))
      (cons (integer->char (remainder integer 128))
            (integer->charlist (quotient integer 128)))))

;;;; the following procedure is handy for timing things
(#%require (only racket/base current-milliseconds))
(define (runtime) (current-milliseconds))

(define (timed f . args)
  (let ((init (runtime)))
    (let ((v (apply f args)))
      (display (list 'time: (- (runtime) init)))
      (newline)
      v)))

;;;; Some initial test data

(define test-key-pair1
  (make-key-pair
   (make-key 816898139 180798509)
   (make-key 816898139 301956869)))

(define test-key-pair2
  (make-key-pair
   (make-key 513756253 416427023)
   (make-key 513756253 462557987)))

;; Implemnent digital signature here

;;; Encrpyt-and-sign to encrpy a message and sign with a recipients public key.
;;; All this function does is store the encrypted message in one variable
;;; after encrypting with the recipients public key. Then it will cons on it with the
;;; RSA converted list of that encrypted message using the private key of the sender.

(define (encrypt-and-sign message senderpriv-key recippub-key)
  (let ((encrypted-message (RSA-encrypt message recippub-key)))
    (cons encrypted-message (car (RSA-convert-list (list (compress encrypted-message)) senderpriv-key)))))


;;; authenticate-and-decrypt
(define (authenticate-and-decrypt signed-message senderpub-key recippriv-key)
  ;;; If the unconverted signature on the message matches the signature of the compressed message
  ;;; then the message is translated using the recipients private key
  ;;; otherwise the keys do not match and false is returned
  (let ((real-sig (compress (car signed-message))))
  (if (= real-sig (car (RSA-unconvert-list (list (cdr signed-message)) senderpub-key)))
      (intlist->string (RSA-unconvert-list (car signed-message) recippriv-key))
      #f)))



;;;public keys for political figures

(define donald-trump-public-key (make-key 833653283 583595407))
(define mike-pence-public-key (make-key 655587853 463279441))
(define nancy-pelosi-public-key (make-key 507803083 445001911))
(define aoc-public-key (make-key 865784123 362279729))
(define michael-cohen-public-key (make-key 725123713 150990017))
(define ivanka-trump-public-key (make-key 376496027 270523157))
(define bernie-sanders-public-key (make-key 780450379 512015071))
(define kamala-harris-public-key (make-key 412581307 251545759))
(define joe-biden-public-key (make-key 718616329 290820109))
(define joe-biden-private-key (make-key 718616329 129033029))

;;;message received by Joe Biden -- Who sent it?
(define received-mystery-message
  '(521793772 221028613 52459926 511097780 523838672 443241014 511806122 640398158 370564768 315158823 38083336 483957005 194461903 678652729))

(define received-mystery-signature 205550182)

;;; trump2pence to fake messages from trump to pence.

(define donald-trump-private-key (crack-rsa donald-trump-public-key))
(define mike-pence-private-key (crack-rsa mike-pence-public-key))
(define trump2pence
    (encrypt-and-sign "Announce that we're increasing taxes by 100%! Biggest increase ever! TREMENDOUS increase!" donald-trump-private-key mike-pence-public-key))

