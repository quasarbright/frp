#lang racket

; An implementation of https://docs.racket-lang.org/kinda-ferpy/index.html

; current weaknesses:
; doesn't handle conditionals well. need to explicitly indicate all dependencies and suffer duplicate evaluation or miss some updates.
; doesn't garbage collect well
; sometimes re-evaluates when not necessary. When a leaf updates, if its value stays the same, it doesn't re-evaluate dependents. However, if an indirect update
; doesn't change a value, its dependents are still re-evaluated.

; there must be a better way to handle automatic dependency collection for conditionals.
; A static variable reference analysis could do it, but how would you do that?
; c = (if (b) (x) (y)) should only depend on x xor y at a time anyway though. How can we make that happen?
; We could update dependents during re-evaluation. But that is incompatible with topological sort, which computes update order before re-evaluating.
; You would get away with it most of the time, but if (b) is true and an update makes it false, it is theoretically possible that y also gets updated, but after
; c.
; You have to choose between re-evaluations and incorrect results.
; Unless you can somehow represent conditional dependencies directly.
; Or what if you only updated dependents if the value actually changed, using an eq? check? Not sure if that'd be compatible with topo sort either though.
;
; After reading FrTime paper:
; According to the FrTime paper, they use bfs with a priority queue where the maximum dependency height of a cell is the priority
; They handle conditionals by changing the graph as it updates, which sounds like a mess. Not interested.
; They seem to do their own gc.
; They handle cycles with a delay operator. This may be simple enough to be worth trying out here.

(module+ examples (provide (all-defined-out)))
(module+ test (require rackunit) (require (submod ".." examples)))
(provide make-cell
         cell-get
         cell-set!
         define-cell
         discovery?)

(require data/queue (for-syntax syntax/parse syntax/transformer))

; data definitions

(struct cell [[val #:mutable] [thnk #:mutable] [dependents #:mutable] [dependencies #:mutable]]
  #:transparent
  #:property prop:procedure
  (case-lambda
    [(c) (cell-get c)]
    ; WARNING: this does not create a derived cell even when it should.
    [(c new-val) (cell-set! c new-val)]))
; A [Cell A] is a
#;(cell A (-> A) (set/c [Cell Any]) (set/c [Cell Any]))
; And represents a reactive computation with a cached value
; val is the cached value
; thnk is the thunk for re-computing val
; dependents contains cells that depend on the value of this cell. (immutable seteq)
; dependencies contains cells that this cell's value depends on. (immutable seteq)
; CONSTRAINT: A Cell must not depend on itself
(module+ examples
  (define-values (two three sum23)
    (shared ([two (cell 2 (const 2) (seteq sum23) (seteq))]
             [three (cell 3 (const 3) (seteq sum23) (seteq))]
             [sum23 (cell 5
                          (lambda () (+ (cell-get two) (cell-get three)))
                          (seteq)
                          (seteq two three))])
      (values two three sum23))))

; functionality

(define-syntax make-cell
  (syntax-parser
    [(_ (~optional (~seq #:dependencies (dependency:expr ...))
                   #:defaults ([(dependency 1) null]))
        body ...)
     #'(make-cell/proc (lambda () body ...) #:dependencies (list dependency ...))]))

#;((-> A) [#:dependencies (listof (Cell Any))] -> (Cell A))
; Create a cell from the thunk.
; Automatically determines implicit dependencies.
; Can optionally supply explicit dependencies as well. This doesn't work with dependencies
; defined with define-cell, but you can just put (void c1 c2 ...) in the body.
(define (make-cell/proc thnk #:dependencies [explicit-dependencies '()])
  ; TODO add support for define-cell.
  (define-values (val implicit-dependencies)
    (with-discovery thnk))
  (define dependencies (set-union (apply seteq explicit-dependencies)
                                  implicit-dependencies))
  (define c (cell val thnk (seteq) dependencies))
  (for ([dependency dependencies])
    (cell-add-dependency! dependency c))
  c)

(module+ test
  (let* ([three (make-cell 3)]
         [two (make-cell 2)]
         [sum23 (make-cell (+ (three) (two)))])
    (check-equal? (cell-val sum23) 5)
    (check-equal? (cell-dependents two) (seteq sum23))
    (check-equal? (cell-dependents sum23) (seteq)))
  (let* ([b (make-cell #t)]
         [three (make-cell 3)]
         [two (make-cell 2)]
         [implicit (make-cell (if (b) (three) (two)))]
         [explicit (make-cell #:dependencies (three two) (if (b) (three) (two)))])
    (check-equal? (cell-val implicit) 3)
    (check-equal? (cell-val explicit) 3)
    (check-equal? (cell-dependents three) (seteq implicit explicit))
    (check-equal? (cell-dependents two) (seteq explicit))))

#;((-> A) -> (values A (set/c (Cell Any))))
; Runs thnk with discovery enabled. Returns the result of thnk and the discovered dependencies.
(define (with-discovery thnk)
  (parameterize ([discovered-dependencies (seteq)])
    (define result (thnk))
    (values result (discovered-dependencies))))

(module+ test
  (let-values ([(result discovered) (with-discovery (lambda () (discover! three) 2))])
    (check-equal? result 2)
    (check-equal? discovered (seteq three))))

; contains the dependencies discovered during discovery. seteq
(define discovered-dependencies (make-parameter #f))

#;(-> boolean?)
; is discovery happening right now?
(define (discovery?) (not (not (discovered-dependencies))))

(module+ test
  (check-equal? (discovery?) #f)
  (let ()
    (with-discovery (lambda () (check-equal? (discovery?) #t)))
    ; This is necessary to avoid printing seteq when tests run
    (void))
  (check-equal? (discovery?) #f))

#;([Cell Any] [Cell Any] -> void?)
; Register `dependent` as a dependent of `dependency` and vice versa.
; TODO swap argument order bc it's confusing
(define (cell-add-dependency! dependency dependent)
  (set-cell-dependents! dependency (set-add (cell-dependents dependency) dependent))
  (set-cell-dependencies! dependent (set-add (cell-dependencies dependent) dependency)))

(module+ test
  (let ([dependency (cell 1 (const 1) (seteq) (seteq))]
        [dependent (cell 1 (const 1) (seteq) (seteq))])
    (cell-add-dependency! dependency dependent)
    (check-equal? (cell-dependents dependency) (seteq dependent))
    (check-equal? (cell-dependencies dependent) (seteq dependency))))

#;([Cell Any] [Cell Any] -> void?)
; Remove `dependent` as a dependent of `dependency` and vice versa.
(define (cell-remove-dependency! dependency dependent)
  (set-cell-dependents! dependency (set-remove (cell-dependents dependency) dependent))
  (set-cell-dependencies! dependent (set-remove (cell-dependencies dependent) dependency)))

#;((Cell A) -> A)
; Get the value of the cell.
; EFFECT: during discovery, adds this cell to discovered dependencies.
(define (cell-get c)
  (when (discovery?) (discover! c))
  (cell-val c))

(module+ test
  (let-values ([(result discovered) (with-discovery (lambda () (cell-get three)))])
    (check-equal? result 3)
    (check-equal? discovered (seteq three)))
  ; also works outside of discovery
  (check-equal? (cell-get three) 3))

#;((Cell A) -> void?)
; Add this cell to the discovered dependencies.
; Assumes we are in discovery
(define (discover! c)
  (discovered-dependencies (set-add (discovered-dependencies) c)))

(define-syntax-rule (cell-set! c new-val) (cell-set!/proc c (lambda () new-val)))

#;((Cell A) (-> A) -> void?)
; Updates the value of c and updates its dependents recursively.
(define (cell-set!/proc c new-val-thnk)
  ; use cell-val instead of cell-get to prevent any discovery weirdness
  (define old-val (cell-val c))
  (define-values (new-val implicit-dependencies)
    (with-discovery new-val-thnk))
  (when (set-member? implicit-dependencies c)
    (error 'cell-set! "a cell cannot depend on itself"))
  (set-cell-val! c new-val)
  (set-cell-thnk! c new-val-thnk)
  (for ([dependency (cell-dependencies c)])
    (cell-remove-dependency! dependency c))
  (for ([dependency implicit-dependencies])
    (cell-add-dependency! dependency c))
  (unless (eq? old-val new-val)
    (cell-update! c)))

#;((Cell A) -> void?)
; Re-evaluate a cell's dependents recursively.
; Cells only get re-evaluated at most once.
(define (cell-update! c)
  (define cells (get-update-order c))
  (for ([cell cells])
    (cell-re-evaluate! cell)))

#;((Cell A) -> (listof (Cell Any)))
; Returns an ordering of cell updates such that each cell is updated only after all of its dependencies are updated.
(define (get-update-order c)
  ; topological sort
  (define visited (mutable-seteq))
  (define visiting (mutable-seteq))
  (define ordering '())
  (define (visit c)
    (cond
      ; this happens in the case of shared dependents
      [(set-member? visited c) (void)]
      [(set-member? visiting c) (error 'get-update-order "cycle encountered in cell dependency graph")]
      [else
       (set-add! visiting c)
       (for ([dependent (cell-dependents c)])
         (visit dependent))
       (set-remove! visiting c)
       (set-add! visited c)
       (set! ordering (cons c ordering))]))
  (visit c)
  ordering)

#;((Cell A) -> void?)
; Re-evaluates the cell (does not update dependents)
(define (cell-re-evaluate! c)
  (set-cell-val! c ((cell-thnk c))))

(define-syntax-rule
  (define-cell name body ...)
  (begin
    (define c (make-cell body ...))
    (define-syntax name
      (make-variable-like-transformer
       #'(cell-get c)
       (syntax-parser
         [((~literal set!) _ v)
          #'(cell-set! c v)])))))

(module+ test
  (test-case "define-cell sum23 change 2"
    (define-cell x 2)
    (define-cell three 3)
    (define-cell sum (+ x three))
    (check-equal? sum 5)
    (set! x 4)
    (check-equal? x 4)
    (check-equal? sum 7))
  (test-case "define-cell set! to derived"
    (define-cell x 2)
    (define-cell y 3)
    (define-cell z x)
    (set! z y)
    (check-equal? z 3)
    (set! y 4)
    (check-equal? z 4)))

(define-syntax-rule
  (let-cell ([v rhs ...] ...) body ...)
  (let ()
    (define-cell v rhs ...)
    ...
    (let () body ...)))

(module+ test
  (test-case "sum23 change 2"
    (define x (make-cell 2))
    (define three (make-cell 3))
    (define sum (make-cell (+ (x) (three))))
    (check-equal? (sum) 5)
    (cell-set! x 4)
    (check-equal? (x) 4)
    (check-equal? (sum) 7))
  (test-case "set! to derived"
    (define x (make-cell 2))
    (define y (make-cell 3))
    (define z (make-cell (x)))
    (cell-set! z (y))
    ; the value should be 3 even if this isn't done fully right
    (check-equal? (z) 3)

    ; z should now depend on y, not x
    (check-equal? (cell-dependencies z) (seteq y))
    (check-equal? (cell-dependents x) (seteq))
    (check-equal? (cell-dependents y) (seteq z))

    (cell-set! y 4)
    ; the value should be updated since y changed
    (check-equal? (z) 4))
  (test-case "set! x x"
    (define x (make-cell 1))
    (check-exn #rx"cannot depend on itself" (lambda () (cell-set! x (x)))))
  (test-case "indirect cycle"
    (define x (make-cell 1))
    (define y (make-cell (add1 (x))))
    (check-exn #rx"cycle encountered" (lambda () (cell-set! x (y)))))
  (test-case "deep diamond"
    ; c is shaped like this:
    ;     ^    ^    ^
    ; c <   ><   ><   ><...> root
    ;     v    v    v
    ; and very indirectly depends on root
    ; with a really naive dfs implementation, this'd have runtime exponential in n because it'd go down every possible path
    (define root (make-cell 1))
    (define depth 100)
    (define c
      (let loop ([c (make-cell (root))] [n depth])
        (cond
          [(zero? n) c]
          [else
           (define x (make-cell (c)))
           (define y (make-cell (c)))
           (loop (make-cell (x) (y)) (sub1 n))])))
    ; make sure everything gets updated.
    (let ([num-updates (length (get-update-order root))])
      (check-true (< (* depth 3) num-updates) (number->string num-updates)))

    (check-equal? (c) 1)
    (cell-set! root 2)
    (check-equal? (c) 2))
  (test-case "re-evaluates at most once"
    (define root (make-cell 1))
    (define deep
      (let loop ([c (make-cell (root))] [n 10])
        (if (zero? n)
            c
            (loop (make-cell (c)) (sub1 n)))))
    (define shallow (make-cell (root)))
    (define num-evals 0)
    ; a single diamond, but one side is way longer than the other.
    ; should cause a bfs implementation to re-evaluate twice or get the wrong answer when you update root
    (define c (make-cell (set! num-evals (add1 num-evals))
                         (+ (deep)
                            (shallow))))
    (cell-set! root 9)
    (check-equal? (c) 18)
    (check-equal? num-evals 2))
  (test-case "doesn't re-evaluate when eq?"
    (define x (make-cell 1))
    (define num-evals 0)
    (define y (make-cell (set! num-evals (add1 num-evals))
                         (x)))
    (cell-set! x 1)
    (check-equal? (y) 1)
    (check-equal? num-evals 1))
  #;
  (test-case "handles conditional dependencies"
    'todo))
