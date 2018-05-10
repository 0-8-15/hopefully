(use extras #;hopefully-intern-atomics)

(cond-expand
 (sometimes
  (import hopefully))
 (else (use hopefully) (import hopefully-intern-atomics)))

(define (dbg l v)
  (format (current-error-port) "D ~a: ~a\n" l v) v)

(import hopefully-intern-atomics hopefully)

(define r (vector 2 2 2 'b 4 'a))
(define r (##sys#make-structure 'soso 2 2 2 'b 4 'a))

(define tnx (new-transaction))

(import (prefix hopefully-intern Xinternal:))
(define s0 (Xinternal:make-tslot-ref tnx r 2))

(let ((v0 (cell-ref s0)))
  (alter! s0 (+ 21 v0))
  (Xinternal:transaction-commit! tnx)
  )

(import hopefully-current)
(define-ac-record obox v)

(define b1 (make-obox 7))
(define b2 (make-obox 6))

(assert (not (eq? b1 b2)))

;; The preferred way: lightweight transactions.  Use cell-ref's
;; instead of plain record accessors.  Note: Create a ref just once!
;; Each ref starts with the initial value, not the in-transaction
;; value.

(define tnx (new-transaction))

(let ((x (obox-v-ref b1 tnx))
      (y (obox-v-ref b2 tnx)))
  (assert (= (cell-ref x) 7))
  (assert (= (cell-ref y) 6))
  (alter! x (* (cell-ref x) (cell-ref y)))
  (Xinternal:transaction-commit! tnx)
  )

;; Check repeated application.
(obox-v-set! b1 7)
(obox-v-set! b2 6)
(let ((tnx (new-transaction)))
  (let ((x (obox-v-ref b1 tnx))
	(y (obox-v-ref b2 tnx)))
    (assert (= (cell-ref x) 7))
    (assert (= (cell-ref y) 6))
    (alter! x (* (cell-ref x) (cell-ref y)))
    (Xinternal:transaction-commit! tnx)
    ))

(let ((mux (make-mutex)) (mux2 (make-mutex)) (mux3 (make-mutex)) (mux4 (make-mutex)))
  (define t1 #f)
  (define t2 #f)
  (mutex-lock! mux)
  (mutex-lock! mux2)
  (mutex-lock! mux3)
  (mutex-lock! mux4)
  ;; FIXME: this is a chicken bug: without the `dbg` the procedure is
  ;; sometimes not called at all.  TBD: boil this down into a
  ;; managable test case.
  ((dbg 'CALL with-current-transaction)
   (lambda ()
     (let ((x (obox-v b1)) (y (obox-v b2)))
       (assert (= x 42))
       (assert (= y 6))
       (dbg 'Initial 'set)
       (set! (obox-v b2) (* x y)) ;; Try generalized set!
       (assert (= (obox-v b2) 252) "initial set")
       (set! t1
	     (thread-start!
	      (lambda ()
		;; Value in other thread is unchanged...
		(assert (= (obox-v b2) 6))
		(mutex-unlock! mux)
		(mutex-lock! mux2 #f #f)
		;; until commited
		(assert (= (obox-v b2) 252)))))
       (ensure thread? t1)
       (set! t2
	     (thread-start!
	      (lambda ()
		(define call-count 0)
		(define expected #f)
		(with-current-transaction
		 (lambda ()
		   (define ct0 (current-transaction))
		   (define ht0 (stmtnx-ht ct0))
		   (dbg "Value in other thread is unchanged..." (stmtnx-id ct0))
		   (set! expected (if (= call-count 0) 6 252))
		   (if (> call-count 0) (dbg "Second round expecting changed value" expected))
		   (set! call-count (add1 call-count))
		   (let ((xx (obox-v-ref b2 (current-transaction))))
		     (assert (= (obox-v b2) expected))
		     (dbg (current-thread) "also in other thread former ref is still unchanged...")
		     (assert (= (cell-ref xx) expected))
		     (mutex-unlock! mux4)
		     (if (= call-count 1) (mutex-lock! mux3 #f #f)) ;; waiting in second invoction will deadlock
		     (dbg "even after commit.  (Note: tests caching of references to fields.)" (stmtnx-id ct0))
		     (assert (eq? (current-transaction) ct0))
		     ;; Kept for historical interest: This fails for
		     ;; chicken because identity-hash does not hash
		     ;; eq? objects to the same value after mutation.
		     #;(let ((tbl (stmtnx-ht ct0)))
		       (unless
			(hash-table? (hash-table-ref/default tbl b2 #f))
			(assert (not (hash-table-fold tbl (lambda (k v i) (or i (eq? k b2))) #f)))))
		     (assert (eq? (obox-v-ref b2 (current-transaction)) xx))
		     (assert (= (cell-ref xx) expected))
		     (assert (= (obox-v b2) expected)))))
		;; After with-current-transaction returns the default transaction is committed.
		(mutex-unlock! mux2)
		)))
       (mutex-lock! mux #f #f)
       (mutex-lock! mux4 #f #f))))
  (mutex-unlock! mux3)
  (thread-join! t1)
  (thread-join! t2))

(obox-v-set! b1 7)
(obox-v-set! b2 6)

;; This needs -D warn-duplicate-ref

(call-with-transaction
 (lambda (tnx)
   (let* ((r1 (obox-v-ref b1 tnx))
	  (r2 (obox-v-ref b1 tnx)))
     (if (eq? r1 r2)
	 (format (current-error-port) "PLEASE CHECK: there should be a 'duplicate ref' warning just before!\n")
	 (format (current-error-port) "NOTE: Duplicate reference checking was disabled for hopefully.\n" )))))

(let ((mux1 (make-mutex 'T1)) (mux2 (make-mutex 'T2))
      (call-count 0))
  (define (step! msg mux1 mux2 val)
    (mutex-unlock! mux1)
    (if (and mux2 (> call-count 0) (< call-count 100)) (mutex-lock! mux2 #f #f))
    (if msg (format (current-error-port) "~a cc ~a ~a\n" msg call-count val))
    val)
  (define t2
    (make-thread
     (lambda ()
       (call-with-transaction
	(lambda (tnx)
	  (if (>= call-count 0) (set! call-count (add1 call-count))
	      (set! call-count (sub1 call-count)))
	  (if (< call-count 100)
	      (let ((a (obox-v-ref b2 tnx))
		    (b (obox-v-ref b1 tnx)))
		;; Normally one should never do this.  We enforce thread
		;; switches during transaction.
		(alter!
		 a
		 (let* ((x (step! "T2 x(b2)" mux1 mux2 (cell-ref a)))
			(y (step! "T2 y(b1)" mux1 mux2 (cell-ref b))))
		   (dbg 'T2Set (+ 23 (* x y)))))
		(step! "T2 trying now to commit" mux1 mux2 (cell-ref a))))))
       (set! call-count (- call-count))
       (step! "T2 done at count" mux1 #f call-count))
     'T2))
  (mutex-lock! mux1 #f #f)
  (mutex-lock! mux2 #f #f)
  (thread-start! t2)
  (call-with-transaction
   (lambda (tnx)
     (if (>= call-count 0) (set! call-count (add1 call-count))
	  (set! call-count (sub1 call-count)))
     (let ((a (obox-v-ref b1 tnx))
	   (b (obox-v-ref b2 tnx)))
       (alter!
	a
	(let* ((x (step! "T1 x(b1)" mux2 mux1 (cell-ref a)))
	       (y (step! "T1 y(b2)" mux2 mux1 (cell-ref b))))
	  (dbg 'T1Set (* x y))))
       (step! "T1 trying now to commit" mux2 mux1 (cell-ref a)))))
  (thread-join! t2)
  (dbg 'M1 (mutex-state mux1))
  (dbg 'M2 (mutex-state mux2))
  (assert (= call-count -3)) ;; -- not defined to be -3, but normally
  (assert (= (obox-v b1) 455))
  (assert (= (obox-v b2) 65)))

(define-record foo bar)
(define baz (make-foo 0))
(define bazi (make-foo 1))
(define foo-mutex (make-mutex))
(define foo2-mutex (make-mutex))

(define (time-locking call-helper n)
  (define t0 (current-milliseconds))
  (do ((i 0 (add1 i)))
      ((= i n)
       (let ((t (- (current-milliseconds) t0)))
	 (format (current-output-port) "Locking ~a op in ~a ms (~a op/ms)\n" n t (/ n t))))
    ;; Chickens compiler optimizations on the do-loop need to be
    ;; broken.  Otherwise the szenario does not match real
    ;; transactions (who's locking the same lock n times in a
    ;; do-loop).  And results become wierd when the optimizer kicks in.
    (call-helper
     (lambda (ignored)
      ;; mutex-lock! without making it owned is, naturally, slightly
      ;; faster then normal locking.
       (mutex-lock! foo-mutex #f #f)
       (mutex-lock! foo2-mutex #f #f)
       (foo-bar-set! baz (+ (foo-bar baz) (foo-bar bazi)))
       (foo-bar-set! bazi (+ 1 (foo-bar bazi)))
       ;;(foo-bar-set! baz (+ (foo-bar baz) (foo-bar bazi))) (foo-bar-set! bazi (+ 1 (foo-bar bazi)))
       (mutex-unlock! foo2-mutex)
       (mutex-unlock! foo-mutex)))))

(define-a-record gbox v)
(define b3 (make-gbox 0))
(define b3i (make-gbox 1))
(define (time-optimitic n)
  (define t0 (current-milliseconds))
  (do ((i 0 (add1 i)))
      ((= i n)
       (let ((t (- (current-milliseconds) t0)))
	 (format (current-output-port) "Optimistic ~a op in ~a ms (~a op/ms)\n" n t (/ n t))))
    (call-with-transaction
     (lambda (tnx)
       (let ((x (gbox-v-ref b3 tnx))
	     (i (gbox-v-ref b3i tnx)))
	 (let ((ni (@ i)))
	   (alter! x (+ (@ x) ni)) 
	   (alter! i (add1 ni))
	   ;;(alter! x (+ (@ x) ni)) (alter! i (add1 ni))
	   ))))))

(obox-v-set! b1 0)
(obox-v-set! b2 1)

(define (time-optimitic-bad n)
  (define t0 (current-milliseconds))
  (do ((i 0 (add1 i)))
      ((= i n)
       (let ((t (- (current-milliseconds) t0)))
	 (format (current-output-port) "Optimistic/current ~a op in ~a ms (~a op/ms)\n" n t (/ n t))))
    (with-current-transaction
     (lambda ()
       (let ((i (obox-v b2)))
	 (obox-v-set! b1 (+ (obox-v b1) i))
	 (obox-v-set! b2 (add1 i)))))))

(define (time-record-access n)
  (define t0 (current-milliseconds))
  (do ((i 0 (add1 i)))
      ((= i n)
       (let ((t (- (current-milliseconds) t0)))
	 (format (current-output-port) "Simple record access ~a op in ~a ms (~a op/ms)\n" n t (/ n t))))
    (foo-bar-set! baz (+ (foo-bar baz) (foo-bar bazi)))
    (foo-bar-set! bazi (+ 1 (foo-bar bazi)))))

(define (time-ac-record-access n)
  (define t0 (current-milliseconds))
  (do ((i 0 (add1 i)))
      ((= i n)
       (let ((t (- (current-milliseconds) t0)))
	 (format (current-output-port) "AC record access outside ~a op in ~a ms (~a op/ms)\n" n t (/ n t))))
    (let ((i (obox-v b2)))
      (obox-v-set! b1 (+ (obox-v b1) i))
      (obox-v-set! b2 (add1 i)))))

(define (time-ac-record-access2 n)
  (define t0 (current-milliseconds))
  (do ((i 0 (add1 i)))
      ((= i n)
       (let ((t (- (current-milliseconds) t0)))
	 (format (current-output-port) "AC record access in trans ~a op in ~a ms (~a op/ms)\n" n t (/ n t))))
    (let ((i (obox-v b2)))
      (obox-v-set! b1 (+ (obox-v b1) i))
      (obox-v-set! b2 (add1 i)))))

(define (run0.3 n)
  (time-record-access n) (gc #t)
  (time-ac-record-access n)  (gc #t)
  (with-current-transaction (lambda () (time-ac-record-access2 n)))  (gc #t)
  )

(define (run3 n)
  (define (call-helper x) (x 1))
  (time-locking call-helper n)
  (gc #t)
  (time-optimitic n)
  (gc #t)
  (time-optimitic-bad n)
  (gc #t)
  )

(do ((i 0 (add1 i)))
    ((= i 10))
  (run0.3 20000))

(do ((i 0 (add1 i)))
    ((= i 10))
  (run3 20000))

#;(do ((i 0 (add1 i)))
    ((= i 1))
  (run3 10))

(dbg 'Done 'success)
(exit 0)
