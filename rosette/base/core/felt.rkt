#lang racket

(require racket/stxparam racket/stxparam-exptime
         (for-syntax racket/syntax syntax/transformer))
(require "term.rkt" "union.rkt" "bool.rkt" "polymorphic.rkt"
         "merge.rkt" "safe.rkt" "lift.rkt" "forall.rkt")
(require (only-in "real.rkt" @>= @> @= @integer? T*->integer?))

; TODO
(provide @ffeq @ff.add @ff.neg @ff.mul
 (rename-out [@felt felt]) @felt? felt? felt-value felt-type
 (rename-out [@finfield finfield]) finfield-prime finfield?)

;; ----------------- Bitvector Types ----------------- ;;

; Cache of all finfield types constructed so far, mapping sizes to types.
(define finfield-types (make-hasheq))

; Returns the finfield type of the given size.
;; TODO change "prime" to "size"
(define (finfield-type prime)
  (assert (exact-positive-integer? prime)
          (argument-error 'finfield "exact-positive-integer?" prime))
  (hash-ref! finfield-types prime (λ () (finfield prime))))

; Represents a finfield type.
(struct finfield (prime)
  #:transparent
  #:property prop:procedure ; Recognizes finfield values of this type.
  (lambda (self v)
    (match v
      [(felt _ (== self)) #t]
      [(term _ (== self)) #t]
      [(union vs t)
       (and (subtype? self t)
            (match vs
              [(list _ ... (cons g (and (? typed?) (app get-type (== self)))) _ ...) g]
              [_ #f]))]
      [_ #f]))
  #:methods gen:type
  [(define (least-common-supertype self other) (if (equal? self other) self @any/c))
   (define (type-name self) (string->symbol (format "finfield~a?" (finfield-prime self))))
   (define (type-applicable? self) #f)
   (define (type-cast self v [caller 'type-cast])
     (match v
       [(felt _ (== self)) v]
       [(term _ (== self)) v]
       [(union (list _ ... (cons gt (and (? typed? vt) (app get-type (== self)))) _ ...) _)
        (assert gt (type-error caller self v))
        vt]
       [_ (assert #f (type-error caller self v))]))
   (define (type-eq? self u v)        (@ffeq u v))
   (define (type-equal? self u v)     (@ffeq u v))
   (define (type-compress self f? ps) (generic-merge* ps))
   (define (type-construct self vs)   (car vs))
   (define (type-deconstruct self v)  (list v))]
  #:methods gen:solvable
  [(define (solvable-default self) (felt 0 self))
   (define (solvable-domain self) null)
   (define (solvable-range self) self)]
  #:methods gen:custom-write
  [(define (write-proc self port m)
     (fprintf port "(finfield ~a)" (finfield-prime self)))])

; Pattern matching for field element types.
(define-match-expander @finfield
  (syntax-rules ()
    [(_ sz) (finfield sz)])
  (make-variable-like-transformer #'finfield-type))

(define (is-finfield? v) (and (typed? v) (finfield? (get-type v))))

;; ----------------- FiniteField Literals ----------------- ;; 

; Represents a field element literal.
(struct felt (value type)
  #:transparent
  #:methods gen:typed
  [(define (get-type self) (felt-type self))]
  #:property prop:custom-print-quotable 'never
  #:methods gen:custom-write
  [(define (write-proc self port mode)
     (match self
       [(felt v (finfield prime))
          (fprintf port "(felt ~a ~a)" v prime)]))])

(define (ureduce x prime)
  (modulo x prime))

(define (sreduce x prime)
  (if (> x (quotient prime 2))
    (- (modulo x prime) prime)
    (modulo x prime)))

(define (make-felt val field-size)
  (assert (and (real? val) (not (infinite? val)) (not (nan? val)))
          (arguments-error 'felt "expected a real, non-infinite, non-NaN number" "value" val))
  (cond [(exact-positive-integer? field-size) 
         (felt (sreduce val field-size) (finfield-type field-size))]
        [(finfield? field-size) 
         (felt (sreduce val (finfield-prime field-size)) field-size)]
        [else 
         (assert #f (arguments-error 'felt "exact-positive-integer? or finfield? type" "field-size" field-size))]))

; Pattern matching for finfield literals.
(define-match-expander @felt
  (syntax-rules ()
    [(_ val-pat type-pat) (felt val-pat type-pat)])
  (make-variable-like-transformer #'make-felt))

(define (@felt? v)
  (match v
    [(? felt?) #t]
    [(term _ (? finfield?)) #t]
    [(union _ (? finfield?)) #t]
    [(union xs (== @any/c))
     (apply || (for/list ([gv xs] #:when (@felt? (cdr gv))) (car gv)))]
    [_ #f]))

;; ----------------- Lifitng Utilities ----------------- ;;

(define (lift-op op)
  (case (procedure-arity op)
    [(1)  (lambda (x) (safe-apply-1 op x))]
    [(2)  (lambda (x y) (safe-apply-2 op x y))]))

(define (finfield-type-error name . args)
  (arguments-error name "expected finfields of same size" "arguments" args))
 
(define (safe-apply-1 op x)
  (match x
    [(? is-finfield?) (op x)]
    [(union xs _)
     (merge+ 
      (let loop ([xs xs])
        (match xs
          [(list) '()]
          [(list (cons gx (? is-finfield? vx)) rest ...)
           (cons (cons gx (op vx)) (loop rest))]
          [(list _ rest ...) (loop rest)]))
      #:unless (length xs) 
      #:error (finfield-type-error (object-name op) x))]
    [_ (assert #f (finfield-type-error (object-name op) x))]))

(define (safe-apply-2 op x y)
  (assert (and (typed? x) (typed? y)) (finfield-type-error (object-name op) x y))
  (match* (x y)
    [((app get-type (? finfield? tx)) _) 
     (if (equal? tx (get-type y))
         (op x y) 
         (op x (type-cast tx y (object-name op))))]
    [(_ (app get-type (? finfield? ty))) 
     (op (type-cast ty x (object-name op)) y)]
    [((union xs _) (union ys _))
     (merge+
      (let loop ([xs xs])
        (match xs
          [(list) '()]
          [(list (cons gx (and (? typed? vx) (app get-type (? finfield? tx)))) rest ...)
           (match ys
             [(list _ ... (cons gy (and (? typed? vy) (app get-type (== tx)))) _ ...)
              (match (&& gx gy)
                [#f (loop rest)]
                [g  (cons (cons g (op vx vy)) (loop rest))])]
             [_ (loop rest)])]
          [(list _ rest ...)
           (loop rest)]))
      #:error (finfield-type-error (object-name op) x y))]
    [(_ _) (assert #f (finfield-type-error (object-name op) x y))]))

(define-syntax-rule (define-lifted-operator @ffop ffop type)
  (define-operator @ffop
    #:identifier 'ffop
    #:range type
    #:unsafe ffop
    #:safe (lift-op ffop)))

;; ----------------- FiniteField Operators ----------------- ;;

; Simplification rules for ff.add
(define (ff.add x y)
  (match* (x y)
    [((felt a t) (felt b _)) (felt (sreduce (+ a b) (finfield-prime t)) t)]
    [((felt 0 _) _) y]
    [(_ (felt 0 _)) x]
    ;; TODO simplify-ff.add:expr/term for optimization
    [(_ _) (sort/expression @ff.add x y)]))

(define (ff.mul x y)
  (match* (x y)
    [((felt a t) (felt b _)) (felt (sreduce (* a b) (finfield-prime t)) t)]
    [((felt 0 _) _) x]
    [((felt 1 _) _) y]
    [((felt -1 _) _) (ff.neg y)]
    [(_ (felt 0 _)) y]
    [(_ (felt 1 _)) x]
    [(_ (felt -1 _)) (ff.neg x)]
    ;; TODO simplify-ff.mul:expr/term for optimization
    [(_ _) (sort/expression @ff.mul x y)]))

(define (ff.neg x)
  (match x
    [(felt v t) (felt (sreduce (- v) (finfield-prime t)) t)]
    [(expression (== @ff.neg) v) v]
    [_ (expression @ff.neg x)]))

(define (ffeq x y) 
  (match* (x y)
    [((felt u t) (felt v _)) (= (ureduce u (finfield-prime t)) (ureduce v (finfield-prime t)))]
    [(_ (== x)) #t]
    ;; TODO these optimizations?
;    [((expression (== ite) a (felt b _) (felt c _)) (felt d _))
;     (|| (&& a (= b d)) (&& (! a) (= c d)))]
;    [((felt d t) (expression (== ite) a (felt b _) (felt c _)))
;     (|| (&& a (= b d)) (&& (! a) (= c d)))]
;    [((expression (== ite) a (felt b t) (felt c _)) (expression (== ite) d (felt e _) (felt f _)))
;     (let ([b=e (= b e)] 
;           [b=f (= b f)] 
;           [c=e (= c e)] 
;           [c=f (= c f)])
;       (or (and b=e b=f c=e c=f)
;           (|| (&& a d b=e) (&& a (! d) b=f) (&& (! a) d c=e) (&& (! a) (! d) c=f))))]
    [(_ _) (sort/expression @ffeq x y)]))


(define-lifted-operator @ff.neg ff.neg T*->T)
(define-lifted-operator @ff.add ff.add T*->T)
(define-lifted-operator @ff.mul ff.mul T*->T)
(define-lifted-operator @ffeq ffeq T*->boolean?)
