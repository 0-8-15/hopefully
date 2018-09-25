(declare
 ;; (unsafe)

 (no-argc-checks)
 (no-bound-checks)
 (no-procedure-checks)
 (local)
 (inline)
 (safe-globals)
 (specialize)
 (strict-types)
)

;; This code should be able to run with interrupts enabled.  But
;; that's quite a slowdown. (And hardly fair when comparing
;; performance to srfi-18 primitives which are compiled with
;; interrupts disabled too).

(include "hopefully-intern-atomics.scm")

;; Note however: with interrupts disabled the commit code could omit
;; one traversal of the list.  FIXME: Is there a feature to test for
;; so we can conditionally skip these section?
(cond-expand
 (with-disable-interrupts
  (declare (disable-interrupts)))
 (no-dirty-tagging
  (set! "conflicting features: (not with-disable-interrupts) vs. no-dirty-tagging"))
 (else))

;; BEWARE: This code depends on srfi-1 being compiled with disable-interrupts
;; Helper procedures which are atomic wrt. srfi-18 threads and (if so
;; documented) signal handlers.

(require-library srfi-1)

;; This use clause disturbs development
;;
;;(use hopefully-intern-atomics)

(module
 hopefully-intern
 *
 (import scheme)
 (import hopefully-intern-atomics)
 (cond-expand
  (chicken-4
   (import chicken)
   (import (only extras random format))
   (use srfi-1 srfi-18))
  (else
   (import (chicken type))
   (import (chicken base))
   (import (chicken condition))
   (import (chicken fixnum))
   (import srfi-1 srfi-18 (only miscmacros ensure))
   (import srfi-28)
   (import (chicken random))
   (define (random x) (pseudo-random-integer x))))

 (define (dbg l v)
   (format (current-error-port) "HD ~a: ~a\n" l v) v)

 (define-record atomic-box hash tag value)

 (define (box value) (make-atomic-box (random 16777216) 2 value))
 (define unbox atomic-box-value)
 (define (box-if/tag! obj old new) (compare-and-set-islot! obj 2 old new)) ; private

 (define-inline (past-txn-begin? txn tag)
   (> tag (stmtnx-id txn)))
 (define-syntax txnclosed? (syntax-rules () ((_ x) (even? x))))
 (define-syntax unhold! (syntax-rules () ((_ x i l) (##sys#setislot x i l))))
 (define-syntax onhold? (syntax-rules () ((_ x) (odd? x))))
 (define-syntax update!
   (syntax-rules ()
     ((_ x i l n)
      (begin
	(##sys#setslot x (add1 i) n)
	(unhold! x i l)))))
 
 (define (box-swap! success box proc . args) ; maybe make success optional
   (ensure atomic-box? box)
   (let ((lock-tag (new-transaction-identifier)))
     (let loop ((old-tag (##sys#slot box 2)))
       (if (onhold? old-tag)
	   (begin
	     (thread-yield!)
	     (loop (##sys#slot box 2)))
	   (let* ((old (##sys#slot box 3))
		  (new (cond
			((null? args) (proc old))
			(else (apply proc old args)))))
	     (if (eq? old new)
		 old
		 (let ((now (compare-and-set-islot! box 2 old-tag lock-tag)))
		   (if (eq? now lock-tag)
		       (begin
			 (update! box 2 (+ old-tag 2) new)
			 (success old new))
		       (loop now)))))))))

 (define-record stmref source slot tag val #;transaction)

 (: %stmref-source ((struct stmref) --> *))
 (: %stmref-slot ((struct stmref) --> fixnum))
 (: %stmref-tag ((struct stmref) --> fixnum))
 (: %stmref-tag-set! ((struct stmref) fixnum --> *))
 (: %stmref-val ((struct stmref) --> *))
 (: %stmref-val-set! ((struct stmref) * --> *))
;; (: %stmref-transaction ((struct stmref) --> (struct stmtnx)))
 (cond-expand
  ((and chicken (not debug))
   (define-inline (%stmref-source cell) (##sys#slot cell 1))
   (define-inline (%stmref-slot cell) (##sys#slot cell 2))
   (define-inline (%stmref-tag cell) (##sys#slot cell 3))
   (define-inline (%stmref-tag-set! cell v) (##sys#setislot cell 3 v))
   (define-inline (%stmref-val cell) (##sys#slot cell 4))
   (define-inline (%stmref-val-set! cell v) (##sys#setslot cell 4 v))
   ;;(define-inline (%stmref-transaction cell) (##sys#slot cell 5))
   )
  (else
   (define-inline (%stmref-source cell) (stmref-source cell))
   (define-inline (%stmref-slot cell) (stmref-slot cell))
   (define-inline (%stmref-tag cell) (stmref-tag cell))
   (define-inline (%stmref-tag-set! cell v) (stmref-tag-set! cell v))
   (define-inline (%stmref-val cell) (stmref-val cell))
   (define-inline (%stmref-val-set! cell v) (stmref-val-set! cell v))
   ;;(define-inline (%stmref-transaction cell) (stmref-transaction cell))
   ))

 ;; I forgot about "make-locative" when I wrote this.  Should probably
 ;; be rewritten.

 (: make-tslot-ref ((struct stmtnx) * fixnum --> (struct stmref)))
 (define (make-tslot-ref transaction source slot) ;; oddly named internal unsafe
   ;; (ensure fixnum? slot)
   (define (make-cell)
     (let* ((tag (##sys#slot source slot))
	    (cell (make-stmref source slot tag (##sys#slot source (add1 slot)) #;transaction)))
       (transaction-extend! transaction cell)
       (assert (eq? (##sys#slot source slot) tag))
       cell))
   (cond-expand
    (warn-duplicate-ref
     ;; This is expensive.  Intented to be a debug feature to aid code transition.
     (if (not (eq? transaction (current-transaction)))
	 (call-with-current-continuation
	  (lambda (k)
	    (let ((ht (stmtnx-ht transaction)))
	      (obj+slot-table-update! ht source slot (lambda () (k #t)))
	      (format (current-error-port) "Warning (hopefully): Duplicate ref on ~a slot ~a\n" source slot))))))
    (else))
   (let ((ht (stmtnx-ht transaction)))
     (if ht
	 (obj+slot-table-update! ht source slot make-cell)
	 (make-cell))))

  (: %cell-ref ((struct stmref) -> *))
  (define-inline (%cell-ref cell)
   #;(if (eq? (%stmref-tag cell) 0)
       (let ((source (%stmref-source cell)) (slot (%stmref-slot cell)))
	 (let loop ((tag (##sys#slot source slot)))
	   (cond
	    ((onhold? tag)
	     (thread-yield!)
	     (loop (##sys#slot source slot)))
	    ;; TBD?: check being overtaken?
	    (else
	     (let* ((val (##sys#slot source (add1 slot)))
		    (now (##sys#slot source slot)))
	       (if (eq? now tag)
		   (begin
		     (%stmref-val-set! cell val)
		     (transaction-extend! (%stmref-transaction cell) cell)
		     (%stmref-tag-set! cell tag)))))))))
   ;; Mabe check that the transaction is not yet completed.
   ;;
   ;; Questionable: also test that the value was not updated elsewhere?
   ;;
   ;; Finally return cell value.
   (%stmref-val cell))

 ;; Obsolete
 (define (make-box-ref transaction box)
   (make-tslot-ref transaction box 1))

 (: cell-ref ((struct stmref) -> *))	; Note: pure, since it may be mutated.
 (define (cell-ref cell)
   (ensure stmref? cell)
   (%cell-ref cell))

 (: %alter! ((struct stmref) * -> *))
 (define-inline (%alter! cell val)
   (%stmref-val-set! cell val)
#|
   (let ((source (%stmref-source cell)) (slot (%stmref-slot cell)))
     (%stmref-val-set! cell val)
     (let ((old (##sys#slot source (add1 slot))))
       (unless
	(eq? val old)
	#;(let ((transaction (%stmref-transaction cell)))
	  (if (not (stmtnx-ht transaction)) ;; handle duplicate refs
	      ;; Order list last write first.  Duplicates (even in
	      ;; different cells) ignored during commit.
	      (transaction-extend! transaction cell)))
	#;(if (eq? (%stmref-tag cell) 0)
	    (begin
	      (transaction-extend! (%stmref-transaction cell) cell)
	      (%stmref-tag-set! cell (##sys#slot source slot)))
	    (let ((transaction (%stmref-transaction cell)))
	      (if (not (stmtnx-ht transaction)) ;; handle duplicate refs
		  ;; Order list last write first.  Duplicates (even in
		  ;; different cells) ignored during commit.
		  (transaction-extend! transaction cell))))
	(%stmref-val-set! cell val))))
|#
   )

 (: alter! ((struct stmref) * -> *))
 (define (alter! cell val)
   (ensure stmref? cell)
   (%alter! cell val))

 (: @ ((struct stmref) --> *))
 (define @ (getter-with-setter cell-ref alter!))

 (: transaction-commit! ((struct stmtnx) -> (or false (struct stmtnx) pair)))
 (define (transaction-commit! transaction)
   #;(if (txnclosed? (%stmtnx-id transaction))
       (error "transaction already closed"))
   #;(if (not (eq? (stmtnx-owner transaction) (current-thread)))
       (error "transaction owned by thread" (stmtnx-owner transaction)))
   (let ((lock-tag (stmtnx-id transaction)))
     (let loop ((refs (stmtnx-refs transaction))
		(dirty '()))
       (if (null? refs)
	   (let ((trigger-handler (current-trigger-handler))
		 ;; `found` needs a type declaration since we compile
		 ;; with -O3, which includes -specialize
		 (found (the (or boolean pair) #f)))
	     (if
	      (or (not trigger-handler)
		  (handle-exceptions
		   ex (begin	;; Conflict. Undo dirty tagging.
			(for-each
			 (lambda (x) (##sys#setislot (%stmref-source x) (%stmref-slot x) (%stmref-tag x)))
			 dirty)
			(transaction-close! transaction) ;; or should this be done elsewhere?
			(raise ex)
			#f)
		   (set! found ((trigger-handler-sync trigger-handler)
				(map (lambda (proc) (proc transaction))
				     (fold (let ((merge (trigger-handler-merge trigger-handler)))
					     (lambda (x i)
					       (merge lock-tag (%stmref-source x) (%stmref-slot x) i)))
					   ((trigger-handler-new trigger-handler))
					   dirty))))
		   #t))
	      (for-each
	       (lambda (x)
		 (let ((source (%stmref-source x)) (slot (%stmref-slot x)))
		   (update! source slot (+ (%stmref-tag x) 2) (%stmref-val x))))
	       dirty))
	     (transaction-close! transaction)
	     (if found
		 (cons (trigger-handler-done trigger-handler) found)
		 transaction))
	   (let ((x (car refs)))
	     (let ((source (%stmref-source x)) (slot (%stmref-slot x)))
	       (let ((tag (##sys#slot source slot)))
		 (cond
		  ((eq? tag lock-tag)
		   ;; Referenced in this transaction later (list is
		   ;; reverse access order).  Ignore prior ref.
		   (cond-expand
		    ((and (not debug) no-dirty-tagging))
		    (else
		     (format (current-error-port) "Warning: 'hopefully' conflict free transaction ran into double reference\n")))
		   (loop (cdr refs) dirty))
		  ((not (eq? tag (%stmref-tag x)))
		   ;; Conflict. Undo dirty tagging.
		   (cond-expand
		    ((and (not debug) no-dirty-tagging))
		    (else
		     (for-each
		      (lambda (x) (##sys#setislot (%stmref-source x) (%stmref-slot x) (%stmref-tag x)))
		      dirty)))
		   (transaction-close! transaction) ;; or should this be done elsewhere?
		   #f)
		  ((eq? (##sys#slot source (add1 slot)) (%stmref-val x))
		   ;; Unchanged, no dirty tagging, no updates.
		   (loop (cdr refs) dirty))
		  (else
		   (cond-expand
		    ((and (not debug) no-dirty-tagging)
		     (loop (cdr refs) (cons x dirty)))
		    (else
		     (if (eq? (compare-and-set-islot! source slot tag lock-tag) lock-tag)
			 (loop (cdr refs) (cons x dirty))
			 (begin	;; Conflict. Undo dirty tagging.
			   (for-each
			    (lambda (x) (##sys#setislot (%stmref-source x) (%stmref-slot x) (%stmref-tag x)))
			    dirty)
			   (transaction-close! transaction) ;; or should this be done elsewhere?
			   #f)))))))))))))

 (define-inline (call-post-triggers! commited)
   ;; Call post triggers if any.
   (if (pair? commited) ((car commited) (cdr commited))))

 (: call-with-current-transaction/values ((procedure () . *) &rest boolean -> . *))
 (define (call-with-transaction/values proc . heavy?)
   (let ((tnx (new-transaction (and (pair? heavy?) (car heavy?)))))
     (let loop ()
       (receive
	results (proc tnx)
	(let ((commited (transaction-commit! tnx)))
	  (if commited
	      (begin
		(call-post-triggers! commited)
		(apply values results))
	      (begin
		(transaction-reopen! tnx)
		(loop))))))))

 (: call-with-current-transaction ((procedure () . *) &rest boolean -> *))
 (define (call-with-transaction proc . heavy?)
   (let ((tnx (new-transaction (and (pair? heavy?) (car heavy?)))))
     (let loop ((x (proc tnx)))
       (let ((commited (transaction-commit! tnx)))
	 (if commited
	     (begin
	       (call-post-triggers! commited)
	       x)
	     (begin
	       (transaction-reopen! tnx)
	       (loop (proc tnx))))))))

 (: with-current-transaction ((procedure () . *) -> . *))
 (define (with-current-transaction thunk)
    (if (current-transaction)
	(thunk)
	(let ((tnx (new-transaction #t)))
	  (let ((x (parameterize
		    ((%current-transaction tnx))
		    (let loop ()
		      (receive
		       results (thunk)
		       #;(if (transaction-commit! tnx)
		       results
		       (begin
		       (transaction-reopen! tnx)
		       (loop)))
		       (let ((post-triggers (transaction-commit! tnx)))
			 (if post-triggers
			     (cons results post-triggers)
			     (begin
			       (transaction-reopen! tnx)
			       (loop)))))))))
	    (call-post-triggers! (cdr x))
	    (apply values (car x))))))

 (: current-slot-ref (* fixnum --> *))
 (define (current-slot-ref source slot) ;; oddly named internal unsafe
   (let ((transaction (current-transaction)))
     (if transaction
	 (%cell-ref (make-tslot-ref transaction source slot))
	 (##sys#block-ref source (add1 slot)))))

 (: alter-current-slot! (* fixnum * -> *))
 (define (alter-current-slot! source slot val)
   (let ((transaction (current-transaction)))
     (if transaction
	 (%alter! (make-tslot-ref transaction source slot) val)
	 (cond-expand
	  (no-dirty-tagging
	   (##core#begin
	    (##sys#block-set! source slot (fx+ (##sys#block-ref source slot) 2))
	    (##sys#block-set! source (add1 slot) val)))
	  (else
	   ;; FIXME: Better use ##sys#setislot for the tag here!
	   (##core#begin
	    (##sys#block-set! source slot (fx+ (##sys#block-ref source slot) 1))
	    (##sys#block-set! source (add1 slot) val)
	    (##sys#block-set! source slot (fx+ (##sys#block-ref source slot) 1))))))))

 )

(module
 hopefully-good
 (cell-ref @ alter! call-with-transaction call-with-transaction/values
  (syntax: define-a-record random))
 (import scheme)
 (cond-expand
  (chicken-4
   (import (only extras random))
   (import chicken hopefully-intern)
   (import-for-syntax srfi-1))
  (else
   (import hopefully-intern)
   (import (chicken syntax))
   (begin-for-syntax (import (chicken fixnum) srfi-1))))
 (define-syntax define-a-record
   (##sys#er-transformer
    (lambda (x r c)
      (##sys#check-syntax 'define-a-record x '(_ symbol . _))
      (let* ((name (cadr x))
	     (slots (cddr x))
	     (prefix (symbol->string name))
	     (%define (r 'define))
	     (%setter (r 'setter))
	     (%getter-with-setter (r 'getter-with-setter))
	     (%fold-right (r 'fold-right))
	     (%current-transaction (r 'current-transaction))
	     (%make-cell (r 'make-tslot-ref))
	     (%cell-ref (r 'cell-ref))
	     (%random (r 'random))
	     (%pair? (r 'pair?))
	     (%car (r 'car))
	     (slotnames slots))
	`(##core#begin
	  (,%define ,name (##sys#make-structure 'atomic-record ',name))
	  (,%define 
	   ,(string->symbol (string-append "make-" prefix))
	   (##core#lambda
	    ,slotnames
	    (##sys#make-structure (##core#quote ,name) (random 16777216) ,@(fold-right (lambda (s i) (cons 2 (cons s i))) '() slotnames))))
	  (,%define
	   ,(string->symbol (string-append prefix "?"))
	   (##core#lambda (x) (##sys#structure? x (##core#quote ,name))) )
	  ,@(let mapslots ((slots slots) (i 2))
	      (if (eq? slots '())
		  slots
		  (let* ((slotname (symbol->string (car slots)))
			 (gett (string->symbol (string-append prefix "-" slotname "-tag")))
			 (getv (string->symbol (string-append prefix "-" slotname)))
			 (getr (string->symbol (string-append prefix "-" slotname "-ref"))))
		    (cons
		     `(##core#begin
		       (,%define
			,gett
			(##core#lambda 
			 (x)
			 (##core#check (##sys#check-structure x (##core#quote ,name)))
			 (##sys#block-ref x ,i) ))
		       (,%define
			,getr
			(##core#lambda
			 (x transaction)
			 (##core#check (##sys#check-structure x (##core#quote ,name)))
			 (,%make-cell transaction x ,i) ))
		       (,%define
			,getv
			(##core#lambda 
			 (x . transaction)
			 (##core#check (##sys#check-structure x (##core#quote ,name)))
			 (if (,%pair? transaction)
			     (,%cell-ref (,%make-cell (,%car transaction) x ,i))
			     (##sys#block-ref x ,(add1 i))) ) ) )
		     (mapslots (##sys#slot slots 1) (fx+ i 2)) ) ) ) ) ) ) ) ) )

 )

(module
 hopefully-current
 (with-current-transaction
  (syntax: define-ac-record random))
 (import scheme)
 (cond-expand
  (chicken-4
   (import (only extras random))
   (import chicken hopefully-intern)
   (use srfi-1)
   (import-for-syntax srfi-1))
  (else
   (import hopefully-intern)
   (import (chicken syntax))
   (begin-for-syntax (import (chicken fixnum) srfi-1))
   (import (chicken module))))
 (reexport (only hopefully-intern with-current-transaction))
 (reexport (only hopefully-intern-atomics current-transaction))

 ;;  Shamelessly stolen from chicken-syntax

 (define-syntax define-ac-record
 (##sys#er-transformer
  (lambda (x r c)
    (##sys#check-syntax 'define-a-record x '(_ symbol . _))
    (let* ((name (cadr x))
	   (slots (cddr x))
	   (prefix (symbol->string name))
	   (%define (r 'define))
	   (%setter (r 'setter))
	   (%getter-with-setter (r 'getter-with-setter))
	   (%fold-right (r 'fold-right))
	   (%current-transaction (r 'current-transaction))
	   (%make-cell (r 'make-tslot-ref))
	   (%current-slot-ref (r 'current-slot-ref))
	   (%alter-current-slot! (r 'alter-current-slot!))
	   (%random (r 'random))
	   (slotnames slots))
      `(##core#begin
	(,%define ,name (##sys#make-structure 'atomic-record ',name))
	(,%define 
	 ,(string->symbol (string-append "make-" prefix))
	 (##core#lambda
	  ,slotnames
	  (##sys#make-structure (##core#quote ,name) (random 16777216) ,@(fold-right (lambda (s i) (cons 2 (cons s i))) '() slotnames))))
	(,%define
	 ,(string->symbol (string-append prefix "?"))
	 (##core#lambda (x) (##sys#structure? x (##core#quote ,name))) )
	,@(let mapslots ((slots slots) (i 2))
	    (if (eq? slots '())
		slots
		(let* ((slotname (symbol->string (car slots)))
		       (gett (string->symbol (string-append prefix "-" slotname "-tag")))
		       (getv (string->symbol (string-append prefix "-" slotname)))
		       (getr (string->symbol (string-append prefix "-" slotname "-ref")))
		       (setv (string->symbol (string-append prefix "-" slotname "-set!"))))
		  (cons
		   `(##core#begin
		     (,%define
		      ,gett
		      (##core#lambda 
		       (x)
		       (##core#check (##sys#check-structure x (##core#quote ,name)))
		       (##sys#block-ref x ,i) ))
		     (,%define
		      ,getr
		      (##core#lambda
		       (x transaction)
		       (##core#check (##sys#check-structure x (##core#quote ,name)))
		       (,%make-cell transaction x ,i) ))
		     (,%define
		      ,setv
		      (##core#lambda
		       (x val)
		       (##core#check (##sys#check-structure x (##core#quote ,name)))
		       (,%alter-current-slot! x ,i val)))
		     (,%define
		      ,getv
		      (,%getter-with-setter
		       (##core#lambda 
			(x)
			(##core#check (##sys#check-structure x (##core#quote ,name)))
			(,%current-slot-ref x ,i) )
		       ,setv) ) )
		   (mapslots (##sys#slot slots 1) (fx+ i 2)) ) ) ) ) ) ) ) ) )
 
 )

(module
 hopefully
 *
 (import scheme)
 (cond-expand
  (chicken-4)
  (else (import (chicken module))))
 (reexport hopefully-good)
 )
