#lang racket/base

(require
  redex/reduction-semantics)
(provide (all-defined-out))

(define-language infernalizeL
  (e t ::= x
     Type
     (infer e)
     (Π (x : t) t) (λ (x : t) e) (e e)
     (Σ (x : t) t) (pair (Σ (x : t) t) e e) (fst e) (snd e))
  (x   ::= variable-not-otherwise-mentioned)
  (Γ ::= ∅ (Γ x : t))
  #:binding-forms
  (λ (x : t) e #:refers-to x)
  (Π (x : t) e #:refers-to x)
  (Σ (x : t) e #:refers-to x)
  (pair (Σ (x : t_0) t_1 #:refers-to x) e_0 e_1 #:refers-to x))

(define-metafunction infernalizeL
  [(subst e x_0 e_0)
   (substitute e x_0 e_0)])

(define (infernalize--> Γ)
  (term-let ([Γ Γ])
    (reduction-relation infernalizeL
      (--> ((λ (x : t) e_0) e_1)
           (subst e_0 x e_1))
      (--> (infer e)
           t
           (judgment-holds (type-infer Γ e t))))))

(define (infernalize-->* Γ)
  (compatible-closure (infernalize--> Γ) infernalizeL e))

(define-metafunction infernalizeL
  [(reduce Γ e)
   ,(car (apply-reduction-relation* (infernalize-->* (term Γ)) (term e)))])

(define-judgment-form infernalizeL
  #:mode (convert I I I)
  #:contract (convert Γ e e)

  [(where e_3 (reduce Γ e_0))
   (where e_3 (reduce Γ e_1))
   --------------
   (convert Γ e_0 e_1)])

(define-judgment-form infernalizeL
  #:mode (valid I)
  #:contract (valid Γ)

  [--------------------
   (valid ∅)]

  [(type-infer Γ t Type)
   --------------------
   (valid (Γ x : t))])

(define-metafunction infernalizeL
  Γ-ref : Γ x -> t or #f
  [(Γ-ref ∅ x) #f]
  [(Γ-ref (Γ x : t) x) t]
  [(Γ-ref (Γ x_0 : t_0) x) (Γ-ref Γ x)])

(define-judgment-form infernalizeL
  #:mode (type-infer I I O)
  #:contract (type-infer Γ e t)

  [(where t (Γ-ref Γ x))
   (valid Γ)
   -----------------------
   (type-infer Γ x t)]

  [(valid Γ)
   -------------------------------
   (type-infer Γ Type Type)]

  [(type-infer (Γ x : t_0) e t)
   -------------------------------------------
   (type-infer Γ (λ (x : t_0) e) (Π (x : t_0) t))]

  [(type-infer Γ t_0 Type)
   (type-check (Γ x : t_0) t Type)
   -------------------------------------
   (type-infer Γ (Π (x : t_0) t) Type)]

  [(type-infer Γ e_0 (Π (x : t_1) t))
   (type-check Γ e_1 t_1)
   --------------------------
   (type-infer Γ (e_0 e_1) (subst t x e_1))]

  [(type-infer Γ e t)
   -----------------------------
   (type-infer Γ (infer e) Type)]

  [(type-infer Γ t_0 Type)
   (type-check (Γ x : t_0) t Type)
   -------------------------------------
   (type-infer Γ (Σ (x : t_0) t) Type)]

  [(type-check Γ e_1 t_1)
   (type-check Γ e_2 (subst t_2 x e_1))
   (type-infer Γ (Σ (x : t_1) t_2) Type)
   (type-check (Γ x : t_1) t_2 Type)
   -------------------------------------
   (type-infer Γ (pair (Σ (x : t_1) t_2) e_1 e_2) (Σ (x : t_1) t_2))]

  [(type-infer Γ e_1 (Σ (x : t_1) t_2))
   -------------------------------------
   (type-infer Γ (fst e_1) t_1)]

  [(type-infer Γ e_1 (Σ (x : t_1) t_2))
   -------------------------------------
   (type-infer Γ (snd e_1) (subst t_2 x (fst e_1)))]
  )

(define-judgment-form infernalizeL
  #:mode (type-check I I I)
  #:contract (type-check Γ e t)

  [(type-infer Γ e t_1)
   (convert Γ t_1 t)
   -----------------
   (type-check Γ e t)])

(module+ test
  (require rackunit)
  ;; The true typeo
  (define-term Γ-test (((((∅ Unit : Type) unit : Unit) Bool : Type) true : Bool) false : Bool))

  (check-true
   (judgment-holds (type-infer Γ-test true Bool)))

  (check-true
   (judgment-holds (type-infer Γ-test false Bool)))

  (check-true
   (judgment-holds (type-infer Γ-test Bool Type)))

  (check-equal?
   (term (reduce Γ-test (infer Bool)))
   (term Type))

  (check-equal?
   (term (reduce Γ-test (infer true)))
   (term Bool)))

;; examples
(module+ test
  ;; Hm. It seems that infer doesn't make sense unless we also have macros—at
  ;; least pattern based macros.
  ;; Can't really define let without macros; encoding as a function doesn't make sense:
  (define-metafunction infernalizeL
    [(let ([x e]) e_0)
     ((λ (x : (infer e)) e_0) e)])

  (check-true
   (judgment-holds (type-check Γ-test (let ([x true]) x) Bool)))

  (check-true
   (judgment-holds (convert Γ-test
                            (let ([x true]) x)
                            ((λ (x : Bool) x) true))))

  (define-metafunction infernalizeL
    [(pair- e_1 e_2)
     (pair- e_1 e_2 as (infer e_2))]
    [(pair- e_1 e_2 as t_2)
     (pair (Σ (x : (infer e_1)) t_2) e_1 e_2)])

  (check-true
   (judgment-holds (type-check Γ-test (pair- true false) (Σ (x : Bool) Bool))))

  ;; Does this simplify the problem of type rule inference?
  ;; It looks like all "leaves" are either pattern variables or calls to infer,
  ;; so doesn't appear any simpler.

  ;; Can we reduce all leaves to instances of A : Type, i.e., to variables of type Type?
  (define-term let-f
    (λ (A : Type)
      (λ (x : A)
        ;; supports dependency in B
        (λ (B : (Π (x : A) Type))
          (λ (f : (Π (x : A) (B x)))
            (f x))))))

  (define-metafunction infernalizeL
    [(let- ([x e]) e_0)
     ;; Hm. Infer can't really work for terms in a context. Need turnstile like
     ;; infer with ctx argument.
     (let-f (infer e) e (?? (infer e_0) ...) (λ (x : (infer e)) e_0))]))
