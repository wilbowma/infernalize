#lang racket/base

(require
  redex/reduction-semantics)
(provide (all-defined-out))

(current-cache-all? #t)

(define-language infernalizeL
  (e t ::= x
     Bool true false (if e e e)
     Type
     (infer e)
     (= e e) (refl e) (subst e e)
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

  [(red Γ ((λ (x : t) e_0) e_1) (substitute e_0 x e_1))]

  [(red Γ (if true e_1 e_2) e_1)]

  [(red Γ (if false e_1 e_2) e_2)]

  [(red Γ (subst (refl t) e) e)])

(define-judgment-form infernalizeL
  #:mode (red* I I O)
  #:contract (red* Γ e e)

  [(red Γ e_0 e_1)
   ---------------- "Red"
   (red* Γ e_0 e_1)]

  [(red* Γ e e_1)
   ------------------------------ "Cong-Infer"
   (red* Γ (infer e) (infer e_1))]

  [(red* Γ e_1 e_11)
   ------------------------------ "Cong-=1"
   (red* Γ (= e_1 e_2) (= e_11 e_2))]

  [(red* Γ e_2 e_21)
   ------------------------------ "Cong-=2"
   (red* Γ (= e_1 e_2) (= e_1 e_21))]

  [(red* Γ e e_1)
   ------------------------------ "Cong-refl"
   (red* Γ (refl e) (refl e_1))]

  [(red* Γ t t_1)
   ------------------------------ "Cong-subst1"
   (red* Γ (subst t e) (subst t_1 e))]

  [(red* Γ e e_1)
   ------------------------------ "Cong-subst2"
   (red* Γ (subst t e) (subst t e_1))]

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
   (red* Γ (pair t e_0 e_1) (pair t e_0 e_11))]

  [(red* Γ e e_0)
   ---------------------------- "Cong-if1"
   (red* Γ (if e e_1 e_2) (if e_0 e_1 e_2))]

  [(red* Γ e_1 e_11)
   ---------------------------- "Cong-if2"
   (red* Γ (if e e_1 e_2) (if e e_11 e_2))]

  [(red* Γ e_2 e_21)
   ---------------------------- "Cong-if3"
   (red* Γ (if e e_1 e_2) (if e e_1 e_21))])

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
   -------------- "≡-red*"
   (convert Γ e_0 e_1)]

  [------------------------ "≡-η1-bool"
   (convert Γ (if e t t) t)]

  [------------------------ "≡-η2-bool"
   (convert Γ t (if e t t))])

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

  [(valid Γ)
   -------------------------
   (type-infer Γ Bool Type)]

  [(valid Γ)
   -------------------------
   (type-infer Γ true Bool)]

  [(valid Γ)
   --------------------------
   (type-infer Γ false Bool)]

  [(type-check Γ e Bool)
;   (type-infer Γ e_1 t)
;   (type-infer Γ e_2 t)
   (type-infer Γ e_1 t_1)
   (type-infer Γ e_2 t_2)
;   (type-infer (Γ x : Bool) t Type)
   --------------------------
   (type-infer Γ (if e e_1 e_2) (if e t_1 t_2))]

  [(type-check Γ e_1 Type)
   (type-check Γ e_2 Type)
   --------------------------
   (type-infer Γ (= e_1 e_2) Type)]

  [(type-check Γ e Type)
   --------------------------
   (type-infer Γ (refl e) (= e e))]

  [(type-infer Γ t (= t_1 t_2))
   (type-infer Γ e t_1)
   --------------------------
   (type-infer Γ (subst t e) t_2)]

  [(type-infer (Γ x : t_0) e t)
   -------------------------------------------
   (type-infer Γ (λ (x : t_0) e) (Π (x : t_0) t))]

  [(type-check Γ t_0 Type)
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

  [(type-check Γ t_0 Type)
   (type-check (Γ x : t_0) t Type)
   -------------------------------------
   (type-infer Γ (Σ (x : t_0) t) Type)]

  [(type-check Γ e_1 t_1)
   (type-check Γ e_2 (substitute t_2 x e_1))
   (type-check Γ (Σ (x : t_1) t_2) Type)
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
  (define-term Γ-test ((∅ Unit : Type) unit : Unit))

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
  Goal: no unification, no manipulating derivations (only rules), no unification.
  Ideally: manipulate only a type and get a simple isomorphism between types and rules.

  Now, can we automagically turn function definitions into type rules, and if
  so, is this some kind of advantage in terms of performance, error reporting,
  or simplicity?

  I think: yes, at least in terms of simplicity.
  Consider the following type, which expresses the typing rule for dependent let:

  Γ ⊢ let-f : (Π (A : Type)
                (Π (x : A)
                  (Π (B : (Π (x : A) Type))
                    (Π (f : (Π (x : A) (B x)))
                      (B x)))))

  And the macro
    (let ([x e]) e_0) =>
    ((((let-f (infer e)) e) (λ (x : (infer e)) (infer e_0))) (λ (x : (infer e)) e_0))

  The type of let-f expresses the typing rule of dependent let as a Type.
  It should tell us that the type of let is:

    ⊢ e : A
    x : A ⊢ e_0 : B
    ---------------------------------
    ⊢ (let ([x e]) e_0) : B[e/x]

  Here's how to perform the transformation:
  1. For the macro, give it the final type `infer` of its definition.
  2. For each sub-expression `e` of the surface macro, add it as a premise with the type `(infer e)`.
  3. For sub-expressions `e_0` that appear under a telescope `x1 : t1, ..., xn : tn`, such as
     in the definition of the macro, append the telescope to the environment for
     `e_0` in the premise so we get `x1 : t1,...,xn : tn ⊢ e_0`.
     For example, in the above example, `e_0` appears under the telescope `x :
     (infer e)`, so we get the premise `x : (infer e) ⊢ e_0`.
  4. Replace each instance of `(infer e)` with a fresh name `A`.
     If that `(infer e)` is itself under a telescope `x : t ...`, replace it by
     an application of `(A x ...)`
  5. From the premises of the type rule, generate telescope θ, replacing any
     pattern variable `e` from the premises that appear under a telescope `x : t ...`
     by `(e x ...)` in the result type.
  6. Evaluate the output of the type rule under θ
  7. If the output type is of the form `(A e ...)`, where x : B ... ⊢ A : Type, rewrite
     `(A e ...)` to a substitution `A[e .../x ...]

  Step-by-step:
  1.
     ---------------------------------
     ⊢ (let ([x e]) e_0) : (infer ((((let-f (infer e)) e) (λ (x : (infer e)) (infer e_0))) (λ (x : (infer e)) e_0)))

  2.
    ⊢ e : (infer e)
    ⊢ e_0 : (infer e_0)
    ---------------------------------
    ⊢ (let ([x e]) e_0) : (infer ((((let-f (infer e)) e) (λ (x : (infer e)) (infer e_0))) (λ (x : (infer e)) e_0)))
  3.
    ⊢ e : (infer e)
    x : (infer e) ⊢ e_0 : (infer e_0)
    ---------------------------------
    ⊢ (let ([x e]) e_0) : (infer ((((let-f (infer e)) e) (λ (x : (infer e)) (infer e_0))) (λ (x : (infer e)) e_0)))
  4.
    ⊢ e : A
    x : A ⊢ e_0 : B
    ---------------------------------
    ⊢ (let ([x e]) e_0) : (infer ((((let-f A) e) (λ (x : A) (B x))) (λ (x : A) e_0)))
  5.
    ⊢ e : A
    x : A ⊢ e_0 : B
    ---------------------------------
    ⊢ (let ([x e]) e_0) : (infer ((((let-f A) e) (λ (x : A) (B x))) (λ (x : A) (e_0 x))))

    θ = (A : Type) (e : A) (B : (Π (x : A) Type)) (e_0 : (Π (x : A) (B x)))
  |#
  ;; Need a little work on transforming telescopes
  (check-equal?
   (term (B e))
   (term (reduce ((((∅ A : Type) e : A) B : (Π (x : A) Type)) e_0 : (Π (x : A) (B x)))
                 (infer ((((let-f A) e) (λ (x : A) (B x))) (λ (x : A) (e_0 x)))))))

  #|
  6.
    ⊢ e : A
    x : A ⊢ e_0 : B
    ---------------------------------
    ⊢ (let ([x e]) e_0) : (B e)
  7.
    ⊢ e : A
    x : A ⊢ e_0 : B
    ---------------------------------
    ⊢ (let ([x e]) e_0) : B[e/x]

  Key telescope isomorphisms:
    x : A ⊢ B : Type <-> B : (Π (x : A) Type)
    x : A ⊢ e : B    <-> ⊢ e : (Π (x : A) (B x))
    (λ (x : A) e)    <-> (λ (x : A) (e x))



  What about the simpler macro?
    (let ([x e]) e_0) => ((λ (x : (infer e)) e_0) e)

  1.
    ---------------------------------
    ⊢ (let ([x e]) e_0) : (infer ((λ (x : (infer e)) e_0) e))
  2.
    ⊢ e : (infer e)
    ⊢ e_0 : (infer e_0)
    ---------------------------------
    ⊢ (let ([x e]) e_0) : (infer ((λ (x : (infer e)) e_0) e))
  3.
    ⊢ e : (infer e)
    x : (infer e) ⊢ e_0 : (infer e_0)
    ---------------------------------
    ⊢ (let ([x e]) e_0) : (infer ((λ (x : (infer e)) e_0) e))
  4.
    ⊢ e : A
    x : A ⊢ e_0 : B
    ---------------------------------
    ⊢ (let ([x e]) e_0) : (infer ((λ (x : A) e_0) e))
  5.
    ⊢ e : A
    x : A ⊢ e_0 : B
    ---------------------------------
    ⊢ (let ([x e]) e_0) : (infer ((λ (x : A) (e_0 x)) e))

    Θ = (A : Type) (e : A) (B : (Π (x : A) Type)) (e_0 : (Π (x : A) (B x)))
  |#
  (check-equal?
   (term (B e))
   (term (reduce ((((∅ A : Type) e : A) B : (Π (x : A) Type)) e_0 : (Π (x : A) (B x)))
                 (infer ((λ (x : A) (e_0 x)) e)))))
  #|
  6.
    ⊢ e : A
    x : A ⊢ e_0 : B
    ---------------------------------
    ⊢ (let ([x e]) e_0) : (B e)
  7.
    ⊢ e : A
    x : A ⊢ e_0 : B
    ---------------------------------
    ⊢ (let ([x e]) e_0) : B[e/x]

  This derives the typing rule, but with considerable less effort.
  I did not need to write out the typing rule explicitly in the absurd high-order way.
  Instead, I write the obvious sugar, and get the right typing rule.


  Let's true or
  |#
  (define-metafunction infernalizeL
    [(or e_1 e_2)
     (let ([x e_1])
       (if x x e_2))])

  #|
  (or e_1 e_2) => (let ([x e_1]) (if x x e_2))

  1.
    ---------------------------------
    ⊢ (or e_1 e_2) : (infer (let ([x e_1]) (if x x e_2)))
  2.
    ⊢ e_1 : (infer e_1)
    ⊢ e_2 : (infer e_2)
    ---------------------------------
    ⊢ (or e_1 e_2) : (infer (let ([x e_1]) (if x x e_2)))
  3.  (nop)
  4.
    ⊢ e_1 : A
    ⊢ e_2 : B
    ---------------------------------
    ⊢ (or e_1 e_2) : (infer (let ([x e_1]) (if x x e_2)))
  5.
    ⊢ e_1 : A
    ⊢ e_2 : B
    ---------------------------------
    ⊢ (or e_1 e_2) : (infer (let ([x e_1]) (if x x e_2)))

    Θ = (A : Type) (e_1 : A) (B : Type) (e_2 : B)
  |#
  (check-equal?
   (term (infer (if e_1 e_1 e_2)))
   (term (reduce ((((∅ A : Type) e_1 : A) B : Type) e_2 : B)
                 (infer (let ([x e_1]) (if x x e_2))))))
  ;; Failure. `or` seems to require unification and "bubbling up" constraints from the derivation.
  ;; Even eta-expansion doesn't quite solve the problem, although it reduces
  ;; the problem to local unification instead of far-away-in-derivation unification.
  #;(define-metafunction infernalizeL
    [(or- e_1 e_2)
     ((((λ (A : Type)
         (λ (x1 : A)
           (λ (x2 : A)
             (if x1 x1 x2))))
       (infer e_1))
       e_1)
      e_2)])
  #|
  What is the type of or?
  I don't really want unification, I want to explicitly express an equality
  about the types of e_1 and e_2.
  |#
  (define-term or-dep-f
    (λ (B : Type)
      (λ (x1 : Bool)
        (λ (x2 : B)
          (if x1 x1 x2)))))

  (check-true
   (judgment-holds (type-check ∅ or-dep-f (Π (B : Type)
                                             (Π (x1 : Bool)
                                                (Π (x2 : B)
                                                   (if x1 Bool B)))))))

  (define-metafunction infernalizeL
    [(or-dep e_1 e_2)
     (((or-dep-f (infer e_2)) e_1) e_2)])

  (check-equal?
   (term true)
   (term (reduce ∅ (or-dep true false))))

  (check-true
   (judgment-holds (type-check ∅ (or-dep true false) Bool)))

  (check-equal?
   (term false)
   (term (reduce ∅ (or-dep false false))))

  (check-true
   (judgment-holds (type-check ∅ (or-dep false false) Bool)))

  (check-equal?
   (term unit)
   (term (reduce Γ-test (or-dep false unit))))

  (check-true
   (judgment-holds (type-check Γ-test (or-dep false unit) Unit)))

  (check-true
   (judgment-holds (type-check (Γ-test x : Bool) (or-dep x unit) (if x Bool Unit))))

  ;;
  (define-term or-bool-f
    (λ (B : Type)
      (λ (x1 : Bool)
        (λ (p : (= B Bool))
          (λ (x2 : B)
            (if x1 x1 (subst p x2)))))))

  (define-metafunction infernalizeL
    [(or-bool e_1 e_2)
     ((((or-bool-f (infer e_2)) e_1) (refl (infer e_2))) e_2)])

  (check-true
   (judgment-holds (type-check ∅ or-bool-f (Π (B : Type)
                                              (Π (x1 : Bool)
                                                 (Π (p : (= B Bool))
                                                    (Π (x2 : B)
                                                       Bool)))))))
  #|
  Hm. Problems:
  1. Running into limitations of Redex's type system implementation.
     Either need proper bi-directional, or additional annotations.
     Until then, η equality doesn't get congruence for free.
     Already had to explicitly write congruence rules for reduction.
     Is there a good way to automatically get congruence while not losing context?
  2. Not sure what I think about necessity of explicit equalities.
     It does explicitly express the type rule, I think... but its awful
     annotation heavy.
     Unification seems pretty useful.
     At least this is pretty proof theoretic, I guess.
  3. The explicit expansion with type annotations also has implication on performance.
     Maybe should separate annotation from functions/abstraction, e.g., add an
     annotation form `(e : A)`.
     This would have a nice analogy with internalizing `infer`.
     OTOH, this quickly breaks the isomorphism between types and typing rules;
     instead terms become typing rules?
     That doesn't seem right...
     Perhaps some other internalization of performance measures is the best way
     to approach this.
  |#


  ;;; Assorted thoughts

  ;; -- Computing type rules?

  #|
  I'm stupid.
  If computation is meant to help us compute the type rules, then why am I not
  using computation to compute types?
  The typing rule should express the static type arguments with type-leve λ, and
  the term arguments as Π.
  |#
  (define-term or-bool-type-constr
    (λ (B : Type)
      (λ (p : (= B Bool))
        (Π (x1 : Bool)
           (Π (x2 : B)
              Bool)))))

  #|
  Now I would like to express the typing rule for `or` as
    or : ((or-bool-type-constr (infer e2) (refl (infer e2))))
  ... this isn't quite right either.
  |#
  #;(define-term or-bool-f2
    (λ (B : Type)
      (λ (x1 : Bool)
      )))

  ;; -- Dual to `infer`

  #|
  `infer` has an interesting property: it translates λ into Π.
  It's always annoyed me a bit that there are two forms of quantification.
  (although I guess some presentations avoid this...)
  Should there by an analogous term that translates Π into λ?
  `refni`

  ⊢ A : Type
  -------------
  ⊢ (refni A) : A


  ⊢ e : A
  -------------
  ⊢ (refni A) ≡ e

  Well. That's absurd. And undecidable.
  But interesting... an internalization of proof search?
  ...
  Or, maybe it's an internalization of a "hole", or axiomitization?
  But isn't that what variables are?
  Why is this different?

  Does have the effect of translating Π to λ

  Γ ⊢ (λ (x : A) (refni B)) : (Π (x : A) B)
  -------------
  Γ ⊢ (refni (Π (x : A) B)) ≡ (λ (x : A) (refni B))

  Probably could recover soundness with a modality.

  Γ ⊢ A : Type
  -------------
  Γ ⊢ (posit A) : (Suppose A)

  Γ ⊢ e1 : (Suppose A)
  Γ, x : A ⊢ e2 : (Suppose B)
  -------------
  Γ ⊢ (bind (x e1) e2) : (Suppose B)

  Γ ⊢ e : A
  ---------------------------
  Γ ⊢ (return e) : (Suppose A)

  Γ ⊢ e1 : (Suppose A)
  Γ ⊢ e2 : A
  -----------------------
  Γ ⊢ (prove e1 e2) : A

  --------------------
  Γ ⊢ (prove (posit A) e2) ≡ e2

  --------------------
  Γ ⊢ (prove (return e1) e2) ≡ e1

  --------------------
  Γ ⊢ (prove (bind (x e1) e2) e3) ≡ (bind (x e1) e2)
  ... not sure


  `prove` looks like a very odd form of application.

  I feel like `bind` should be:

  Γ ⊢ e1 : (Suppose A)
  Γ, x : A ⊢ e2 : B
  -------------
  Γ ⊢ (bind (x e1) e2) : (Suppose B)

  But this... this must be unsound.

  All of this (`infer` included) looks like something I'm seen before.
  Need to do some reading.
  |#


  #|
  Back to first principles.

  What is a primitive?
  In a language without effects? Simply a function.
  But as soon as we have any effect (e.g., performance), not so simple.
  It's functional behavior is a function, but its other aspects?

  What is a typing rule for a primitive?
  The type of the function (i.e., a Π type), describing the types and scope of
  each sub-expression, and culminating in a result type for the expression when
  fully instantiated.

  f : Π (x : A) ... B

  ≡

  ⊢ e : A[e ...-1 /x ...-1] ...
  ---------
  ⊢ (f e ...) : B[e .../x ...]

  Only true if types are expressive as judgments, and dependent type theory is close

  But this ignores "effects"? E.g. the annotation burden, the effect of inference or unification...?
  |#
)
