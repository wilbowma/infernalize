#lang racket/base

(require
  redex/reduction-semantics)
(provide (all-defined-out))

(current-cache-all? #t)

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

(define-judgment-form infernalizeL
  #:mode (red I I O)
  #:contract (red Γ e e)

  [(type-infer Γ e t)
   ---------------
   (red Γ (infer e) t)]

  [---------------
   (red Γ ((λ (x : t) e_0) e_1) (substitute e_0 x e_1))])

(define-judgment-form infernalizeL
  #:mode (red* I I O)
  #:contract (red* Γ e e)

  [(red Γ e_0 e_1)
   ---------------- "Red"
   (red* Γ e_0 e_1)]

  [(red* Γ t t_0)
   ----------------------------------------- "Cong-Bind1"
   (red* Γ (any_b (x : t) e) (any_b (x : t_0) e))]

  [(red* (Γ x : t) e e_0)
   ----------------------------------------- "Cong-Bind2"
   (red* Γ (any_b (x : t) e) (any_b (x : t) e_0))]

  [(red* Γ e_0 e_01)
   ----------------------------------------- "Cong-App1"
   (red* Γ (e_0 e_1) (e_01 e_1))]

  [(red* Γ e_1 e_11)
   ----------------------------------------- "Cong-App2"
   (red* Γ (e_0 e_1) (e_0 e_11))]

  [(red* Γ e e_0)
   ---------------------------- "Cong-snd"
   (red* Γ (snd e) (snd e_0))]

  [(red* Γ e e_0)
   ---------------------------- "Cong-fst"
   (red* Γ (fst e) (fst e_0))]

  [(red* Γ t t_1)
   ---------------------------- "Cong-pair1"
   (red* Γ (pair t e_0 e_1) (pair t_1 e_0 e_1))]

  [(red* Γ e_0 e_01)
   ---------------------------- "Cong-pair2"
   (red* Γ (pair t e_0 e_1) (pair t e_01 e_1))]

  [(red* Γ e_1 e_11)
   ---------------------------- "Cong-pair3"
   (red* Γ (pair t e_0 e_1) (pair t e_0 e_11))])

(define-judgment-form infernalizeL
  #:mode (red/io* I O)
  #:contract (red/io* (Γ e) (Γ e))

  [(red* Γ e e_1)
   --------------------
   (red/io* (Γ e) (Γ e_1))])

(define-metafunction infernalizeL
  reduce : Γ e -> e
  [(reduce Γ e)
   e_1
   (where (_ e_1) ,(car (apply-reduction-relation* red/io* (term (Γ e)))))])

(define-judgment-form infernalizeL
  #:mode (convert I I I)
  #:contract (convert Γ e e)

  [(where e_2 (reduce Γ e_0))
   (where e_2 (reduce Γ e_1))
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
   (type-infer Γ (e_0 e_1) (substitute t x e_1))]

  [(type-infer Γ e t)
   -----------------------------
   (type-infer Γ (infer e) Type)]

  [(type-infer Γ t_0 Type)
   (type-check (Γ x : t_0) t Type)
   -------------------------------------
   (type-infer Γ (Σ (x : t_0) t) Type)]

  [(type-check Γ e_1 t_1)
   (type-check Γ e_2 (substitute t_2 x e_1))
   (type-infer Γ (Σ (x : t_1) t_2) Type)
   (type-check (Γ x : t_1) t_2 Type)
   -------------------------------------
   (type-infer Γ (pair (Σ (x : t_1) t_2) e_1 e_2) (Σ (x : t_1) t_2))]

  [(type-infer Γ e_1 (Σ (x : t_1) t_2))
   -------------------------------------
   (type-infer Γ (fst e_1) t_1)]

  [(type-infer Γ e_1 (Σ (x : t_1) t_2))
   -------------------------------------
   (type-infer Γ (snd e_1) (substitute t_2 x (fst e_1)))]
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
  (define-term Γ-test (((((∅ Unit : Type) unit : Unit) Bool : Type) true : Bool) false : Bool))

  (check-true
   (judgment-holds (type-infer Γ-test true Bool)))

  (check-true
   (judgment-holds (type-infer Γ-test false Bool)))

  (check-true
   (judgment-holds (type-infer Γ-test Bool Type)))

  (check-true
   (judgment-holds (red* Γ-test (infer Bool) Type)))

  (check-true
   (judgment-holds (red* Γ-test (infer true) Bool))))

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

  ;; Can we reduce all leaves to instances of A : Type, i.e., to variables of type Type (or telescope over Type)?
  (define-term let-f
    (λ (A : Type)
      (λ (x : A)
        ;; supports dependency in B
        (λ (B : (Π (x : A) Type))
          (λ (f : (Π (x : A) (B x)))
            (f x))))))

  (define-metafunction infernalizeL
    [(let- ([x e]) e_0)
     ((((let-f (infer e)) e) (λ (x : (infer e)) (infer e_0))) (λ (x : (infer e)) e_0))])

  (check-true
   (judgment-holds (type-check Γ-test (infer (λ (x : (infer true)) x)) Type)))

  (check-true
   (judgment-holds (type-check Γ-test (λ (x : (infer true)) x) (Π (x : Bool) Bool))))

  (check-true
   (judgment-holds (type-check Γ-test let-f (Π (x_A : Type)
                                               (Π (x : x_A)
                                                  (Π (x_B : (Π (x_0 : x_A) Type))
                                                     (Π (x_f : (Π (x_1 : x_A) (x_B x_1)))
                                                        (x_B x))))))))

  (check-true
   (judgment-holds (type-check Γ-test (let-f (infer true))
                               (Π (x : Bool)
                                  (Π (x_B : (Π (x_0 : Bool) Type))
                                     (Π (x_f : (Π (x_1 : Bool) (x_B x_1)))
                                        (x_B x)))))))

  (check-true
   (judgment-holds (type-check Γ-test ((let-f (infer true)) true)
                               (Π (x_B : (Π (x_0 : Bool) Type))
                                  (Π (x_f : (Π (x_1 : Bool) (x_B x_1)))
                                     (x_B true))))))

  (check-true
   (judgment-holds (type-check Γ-test (λ (x : (infer true)) (infer x)) (Π (x : Bool) Type))))

  (check-true
   (judgment-holds (type-check Γ-test (((let-f (infer true)) true) (λ (x : (infer true)) (infer x)))
                               (Π (x_f : (Π (x_1 : Bool) Bool))
                                  Bool))))

  (check-true
   (judgment-holds (type-check Γ-test (let- ([x true]) x) Bool)))

  #|
  Okay, so this works.
  Now, can we automagically turn function definitions into type rules, and if
  so, is this some kind of advantage in terms of performance or error reporting?
  E.g., given the type of let-f:
  Γ ⊢ let-f : (Π (x_A : Type)
                (Π (x : x_A)
                  (Π (x_B : (Π (x_0 : x_A) Type))
                    (Π (x_f : (Π (x_1 : x_A) (x_B x_1)))
                      (x_B x)))))
  Can we automatically derive:
    Γ ⊢ e : A
    Γ ⊢ f : (Π (x : A) B)
    Γ,x:A ⊢ B : Type (redundant)
    -------------------
    Γ ⊢ let-f e f : B[e/x]

  This would almost separate the concerns of expressing the macros from expressing new typing rules.

  But how do we know which arguments are supposed to be surface and which are not?
  If this is a modality of some kind, could use some tag on Types, e.g.,:
    Γ ⊢ let-f : (Π (A : (Inferred Type))
                  (Π (e : A)
                    (Π (B : (Inferred (Π (x : A) Type)))
                      (Π (f : (Π (x : A) (B x)))
                        (B e)))))

  (Hm. But then, how is this different than internalizing unification?)

  Strategy: first, turn the telescope into a typing rule as follows

  ⊢ A : Inferred Type
  ⊢ e : A
  ⊢ B : (Inferred (Π (x : A) Type))
  ⊢ f : Π (x : A) (B x)
  -----------------------
  ⊢ let-f A e B f : (B e)

  Next, remove Inferred arguments from the surface syntax

  ⊢ A : Inferred Type
  ⊢ e : A
  ⊢ B : (Inferred (Π (x : A) Type))
  ⊢ f : Π (x : A) (B x)
  -------------------
  ⊢ let-f e f : (B e)

  Next, transform Inferred binding types into substitutions

  ⊢ A : Inferred Type
  ⊢ e : A
  x' : A ⊢ B : Inferred Type
  ⊢ f : Π (x : A) B[x/x']
  -------------------
  ⊢ let-f e f : B[e/x']

  Remove all Inferred Types

  ⊢ e : A
  ⊢ f : Π (x : A) B[x/x']
  -------------------
  ⊢ let-f e f : B[e/x']


  ... So this prevents any strange search, I suppose.
  But what did that have to do with the infer term?
  And the resulting syntax is still not the surface syntax.
  Also, it was all at the meta-level, manipulating derivations.
  Want to manipulate terms (or, types) as typing rules.

  If we just suppose pattern-based macros, then how does `infer` simplify
  the resugaring problem:

  Goal: no unification, no manipulating derivations, no unification.
    (let- ([x e]) e_0) =>
    ((((let-f (infer e)) e) (λ (x : (infer e)) (infer e_0))) (λ (x : (infer e)) e_0))

  Tells us the typing rule is:
  ⊢ e : (infer e)
  x : (infer e) ⊢ e_0 : (infer e_0)
  ---------------------------------
  ⊢ (let- ([x e]) e_0) : (infer ((((let-f (infer e)) e) (λ (x : (infer e)) (infer e_0))) (λ (x : (infer e)) e_0)))

  (requires some knowledge of telescopes to transform lambdas into binding premises)

  Need: some normalization step to remove (infer _)'s from generated typing rules
  Think the logic is:
  In a derivation D of the form
     ⊢ e : (infer e) ....
     ---------------------
     .....
     =>
     ⊢ e : A .... [A/(infer e)] (fresh A)
     -----------------------
     ..... [A/(infer e)]
  So we get
  ⊢ e : A
  x : A ⊢ e_0 : B
  ---------------------------------
  ⊢ (let- ([x e]) e_0) : (infer ((((let-f A) e) (λ (x : A) B)) (λ (x : A) e_0)))
  |#
  (displayln
   ())

  )
