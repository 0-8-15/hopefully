(declare
 ;; (unsafe)
 ;;
 ;; This code MUST be compiled with interrupts disabled for atomicity.
 (disable-interrupts)

 (no-argc-checks)
 (no-bound-checks)
 (no-procedure-checks)
 (safe-globals)
 (inline)
 (specialize)
 (strict-types)
)

;; Helper procedures which are atomic wrt. srfi-18 threads and (if so
;; documented) signal handlers.

(module
 hopefully-intern-atomics
 *
 (import scheme)
 (cond-expand
  (chicken-4
   (import chicken (only data-structures identity))
   (use srfi-18))
  (else
   (import (chicken type))
   (import (chicken base))
   (import (chicken fixnum))
   (import srfi-18)))
 
 (define new-transaction-identifier
   (let ((n 1))
     (lambda ()
       (let ((r n))
	 (set! n (fx+ n 2))
	 (assert (not (eq? n 1)))	; overflow not yet handled
	 r))))

 (define-record stmtnx id refs ht owner)

 (: %stmtnx-id ((struct stmtnx) --> fixnum))
 (: %stmtnx-id-set! ((struct stmtnx) fixnum --> *))
 (: %stmtnx-refs ((struct stmtnx) --> (list-of (struct stmref))))
 (: %stmtnx-refs-set! ((struct stmtnx) (list-of (struct stmref)) --> *))
 (: %stmtnx-ht ((struct stmtnx) --> *))
 (: %stmtnx-ht-set! ((struct stmtnx) * --> *))
 (: %stmtnx-owner ((struct stmtnx) --> (struct thread)))
 (cond-expand
  ((and chicken (not debug))
   (define-inline (%stmtnx-id cell) (##sys#slot cell 1))
   (define-inline (%stmtnx-id-set! cell v) (##sys#setislot cell 1 v))
   (define-inline (%stmtnx-refs cell) (##sys#slot cell 2))
   (define-inline (%stmtnx-refs-set! cell v) (##sys#setslot cell 2 v))
   (define-inline (%stmtnx-ht cell) (##sys#slot cell 3))
   (define-inline (%stmtnx-ht-set! cell v) (##sys#setslot cell 3 v))
   (define-inline (%stmtnx-owner cell) (##sys#slot cell 4))
   )
  (else
   (define-inline (%stmtnx-id cell) (stmtnx-id cell))
   (define-inline (%stmtnx-id-set! cell v) (stmtnx-id-set! cell v))
   (define-inline (%stmtnx-refs cell) (stmtnx-refs cell))
   (define-inline (%stmtnx-refs-set! cell v) (stmtnx-refs-set! cell v))
   (define-inline (%stmtnx-ht cell) (stmtnx-ht cell))
   (define-inline (%stmtnx-ht-set! cell v) (stmtnx-ht-set! cell v))
   (define-inline (%stmtnx-owner cell) (stmtnx-owner cell))
   ))


 (define %current-transaction
   (make-parameter #f))

 (define (current-transaction)
   (and-let*
    ((ct (%current-transaction))
     ((eq? (%stmtnx-owner ct) (current-thread))))
    ct))

 ;; Triggers are experimental.

 (define-record trigger-handler new merge sync done)
 
 (define current-trigger-handler (make-parameter #f))

 ;; #### Work around Chicken hash tables not supporting arbitrary
 ;; objects as keys.
 (cond-expand
  ;; This would be the code to use if we could use mutable objects as
  ;; table keys.  BEWARE: Using the chicken specific extension to
  ;; srfi-69 where hash-table-update! returns the new value (instead
  ;; of an undefined value.)
  ;;
  ;; However it is not worth it.  This makes heavy transactions
  ;; roughly 4x as expensive as the llrb based version below.
  (hash-table-hash-mutable-keys
   (define (make-object-table) (make-hash-table eq?))
   (define object-table-update! hash-table-update!)
   )
  ;; Objects (atomic records are the only type of objects allowed here
  ;; anyway) MUST be known to comply with the convention that the
  ;; first slot hold the hash key.
  (chicken
   ;; OK, since it does not make sense that llrb could actually be
   ;; faster than a hash table, let's roll our own.
   ;;
   ;; How many distinct objects each holding possibly multiple
   ;; transactional slots do we expect within a transaction?  SRFI-69
   ;; starts with prime 307, but that turns out to get us down from 19
   ;; to 16 ops/ms - probably gc and initialization.  Since we expect
   ;; a very low number and 31 is still running at 17-18 we use 7,
   ;; which results in 19-20 ops/ms.
   ;;
   ;; Note however that this may not be stable for large transactions.
   ;; If things degrade, we should switch to something smarter; left
   ;; TBD for now.
   (define-constant object-table-modulus 7)
   ;;(define make-object-table fixnum-make-table)
   (define (make-object-table) (make-vector object-table-modulus '()))
   (define (object-table-update! t obj ignored default)
     #;(let* ((bucket (let ((key (##sys#slot obj 1)))
		      (fixnum-table-ref
		       t key
		       (lambda ()
			 (let ((bucket (list #f)))
			   (fixnum-table-set! t key bucket)
			   bucket)))))
	    (node (assq obj (##sys#slot bucket 1))))
       (if node (cdr node)
	   (let ((val (default)))
	     (set-cdr! bucket (cons (cons obj val) (cdr bucket)))
	     val)))

     (let* ((key (##sys#slot obj 1))
	    (offset (fxmod key object-table-modulus))
	    (bucket (##sys#slot t offset))
	    (node (assq obj bucket)))
       (if node (cdr node)
	   (let ((val (default)))
	     (##sys#setslot t offset (cons (cons obj val) bucket))
	     val)))

     ;; This line would be all we need, if we where to opt for unique
     ;; object numbers in slot 1 instead of random ones.  This is here
     ;; currently about 10% faster.  But it does not handle the
     ;; overflow.  Would this ever happend?  (Turns out to be slower, forget it.)
     ;;
     ;;(fixnum-table-update! t (##sys#slot obj 1) ignored default)
     )
   )
  ;; Fallback using hash tables.
  (else
   (define (make-object-table)
     (make-hash-table eq? (lambda (x bound) (fxmod (##sys#slot x 1) bound))))
   (define object-table-update! hash-table-update!)
   ))

 (define (obj+slot-table-update! t obj slot default)
   #;(let ((st (object-table-update! t obj identity fixnum-make-table)))
     (fixnum-table-update! st slot identity default))
   ;; Assuming more knowledge about objects to safe a whole tree walk.
   ;; (Up from 10 to 15 ms^-1 in test benchmark.  Keeping this version
   ;; for now.)
   (let* ((st (object-table-update!
	       t obj identity
	       (lambda () (make-vector (sub1 (fx/ (##sys#size obj) 2)) #f))))
	  (i (sub1 (fx/ slot 2))))
     (or (##sys#slot st i)
	 (let ((v (default)))
	   (##sys#setslot st i v)
	   v)))
   )
 
 (define (new-transaction . x)
   (make-stmtnx
    (new-transaction-identifier)
    '()
    (cond-expand
    (warn-duplicate-ref
     (make-object-table))
    (else
     (and (pair? x) (car x) (make-object-table))))
    (current-thread)))

 (cond-expand
  (debug
   (define (transaction-extend! t r)
     (cond-expand
      (debug
       (if (even? (%stmtnx-id t))
	   (error "transaction already closed"))
       (if (not (eq? (%stmtnx-owner t) (current-thread)))
	   (error "transaction owned by thread" (%stmtnx-owner t))))
      (else))
     (%stmtnx-refs-set! t (cons r (%stmtnx-refs t))))
   )
  (else
   (define-inline (transaction-extend! t r)
     (%stmtnx-refs-set! t (cons r (%stmtnx-refs t))))))

 (define (transaction-reset! t)
   (stmtnx-refs-set! t '())
   (%stmtnx-ht-set! t (and (%stmtnx-ht t) #t)))
 (define (transaction-close! t)
   (%stmtnx-id-set! t (add1 (stmtnx-id t)))
   (transaction-reset! t))

 (define (transaction-reopen! t)
   (assert (even? (stmtnx-id t)))
   (%stmtnx-id-set! t (sub1 (%stmtnx-id t)))
   (if (%stmtnx-ht t)
       (%stmtnx-ht-set! t (make-object-table))))

 ;;(define (slot-ref obj n) ...)

 ;; Named after the Clojure equivalent for atoms.
 (: compare-and-set-slot! (* fixnum * * -> *))
 (define (compare-and-set-slot! obj n old new)
   (assert (not (eq? old new)))		; contract
   (let ((current (##sys#slot obj n)))
     (if (eq? old current)
	 (begin
	   (##sys#setslot obj n new)
	   new)
	 current)))

 (: compare-and-set-islot! (* fixnum * * -> *))
 (define (compare-and-set-islot! obj n old new)
   ;; contract
   (cond-expand
    (debug
     (assert (not (eq? old new))))
    (else))
   (let ((current (##sys#slot obj n)))
     (if (eq? old current)
	 (begin
	   (##sys#setislot obj n new)
	   new)
	 current)))
 
 )
