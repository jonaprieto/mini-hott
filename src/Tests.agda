
module Tests where
  open import BasicFunctions
  open import TransportLemmas
  open import EquivalenceType
  open import QuasiinverseType
  open import QuasiinverseLemmas
  open import HLevelTypes
  open import HLevelLemmas
  open import UnivalenceAxiom
  open import CoproductIdentities

  equiv-is-inj
    : {ℓ₁ ℓ₂ : Level} {A : Type ℓ₁}{B : Type ℓ₂}
    → (f : A → B) → isEquiv f
    → ∀ {x y : A} → (f x ≡ f y) → x ≡ y

  equiv-is-inj {A = A}{B} f f-is-equiv fx≡fy = ! cr · (ap f^-1 fx≡fy · cr)
    where
    f^-1 : B → A
    f^-1 = remap (f , f-is-equiv)

    cr : ∀ {x : A} → f^-1 (f x) ≡ x
    cr = rlmap-inverse (f , f-is-equiv)

  module _ {ℓ : Level} {A : Type ℓ} where
    equiv-induction
        : (P : (C : Type ℓ) → (A ≃ C) → Type ℓ)
        → P A idEqv
        → (C : Type ℓ)
        → (e : A ≃ C)
        -----------------------------
        → P C e

    equiv-induction P p-refl C e  = tr (P C) (ua-β e) g
      where
      open import HLevelLemmas
      P' :  (C : Type ℓ) → A ≡ C → Type ℓ
      P' C p = P C (idtoeqv p)

      b' : P A (idtoeqv idp)
      b' = tr (P A) (sameEqv idp) p-refl


      f' : (C : Type ℓ) → (p : A ≡ C) → P C (idtoeqv p)
      f' C idp = b'

      g : P C (idtoeqv (ua e))
      g = f' C (ua e)

    postcomp-is-equiv
      : (B : Type ℓ)
      → (e : A ≃ B)
      → ∀ {C : Type ℓ}
      → isEquiv {A = C → A} {B = C → B} (_:> (e ∙→))

    postcomp-is-equiv  B e
      = equiv-induction (λ C A≃C → isEquiv (_:> (A≃C ∙→) )) base-case B e
      where
      base-case : isEquiv (λ f x → π₁ idEqv (f x))
      base-case = π₂ idEqv


    postcomp-≃
      : (B : Type ℓ)
      → (e : A ≃ B)
      → (X : Type ℓ)
      → (X → A) ≃ (X → B)
    postcomp-≃ B e X  = (_:> (e ∙→)) , postcomp-is-equiv B e

    postcomp-is-inj
      : (B : Type ℓ)
      → (e : A ≃ B)
      → {C : Type ℓ}
      → (f g : C → A)
      → f :> (e ∙→) ≡ g :> (e ∙→)
      → f ≡ g

    postcomp-is-inj B e f g p =
      equiv-is-inj (_:> (e ∙→)) (postcomp-is-equiv B e) p

  --  The naive non-dependent function extensionality axiom
  funext'
    : {ℓ : Level} {A : Type ℓ}{B : Type ℓ}
    → (f g : A → B)
    → (h : ∏[ x ∶ A ] (f x ≡ g x))
    → f ≡ g

  funext' {A = A}{B} f g h = ap (_:> p₁) d≡e
    where
    d e : A → ∑[ (x , y ) ∶ (B × B) ] (x ≡ y)
    d = λ x → ((f x , f x)) , refl (f x)
    e = λ x → ((f x , g x)) , h x

    p₀ : ∑[ (x , y ) ∶ (B × B) ] (x ≡ y) → B
    p₀ ((x , y) , p) = x

    p₁ : ∑[ (x , y ) ∶ (B × B) ] (x ≡ y) → B
    p₁ ((x , y) , p) = y

    p₀-is-equiv : isEquiv p₀
    p₀-is-equiv
      = π₂ (qinv-≃ p₀ ((λ x → ((x , x) , (refl x) )) ,
          (λ {p → idp}) , (λ {((x , .x) , idp) → idp})))

    d:>p₀≡e:>p₀ : (d :> p₀) ≡ (e :> p₀)
    d:>p₀≡e:>p₀ = idp

    d≡e : d ≡ e
    d≡e = postcomp-is-inj B (p₀ , p₀-is-equiv) d e d:>p₀≡e:>p₀

  -- naive-funext implies weak extensionality:

  open import FibreType
  open import EquivalenceReasoning

  left-universal-property-of-idenity-type
    : {ℓ₁ ℓ₂ : Level} {A : Type ℓ₁}{B : A → Type ℓ₂}
    → (a x : A)
    → (∑[ p ∶ a ≡ x ] B a) ≃  (∑[ b ∶ B a ] a ≡ x)
  left-universal-property-of-idenity-type a x
    = qinv-≃ f (g , ((λ {(_ , idp) → idp}) , λ { (idp , π₄) → idp}))
    where
    f = λ {(idp , b) → (b , idp)}
    g = λ {(b , p) → (p , b)}

  universal-property-of-identity-type
    : {ℓ₁ ℓ₂ : Level} {A : Type ℓ₁}{B : A → Type ℓ₂}
    → (x : A)
    → B x ≃ (∑[ a ∶ A ] ∑[ p ∶ a ≡ x ] B a)
  universal-property-of-identity-type x = qinv-≃ f (g , (λ { (a , idp , π₄) → idp})  , λ {p → idp})
    where
    f = λ b → (x , (refl x , b))
    g = λ {(a , (idp , b)) → b}

  contr-fibers-gives-pr₁-equiv
    : {ℓ₁ ℓ₂ : Level} {A : Type ℓ₁}{B : A → Type ℓ₂}
    → ((x : A) → isContr (B x)) → (pr₁ {A = A}{B}) is-equiv
  contr-fibers-gives-pr₁-equiv {A = A}{B} Bx-is-contr
    = λ x → equiv-preserves-contr (calculation x) (Bx-is-contr x)
    where
    open import SigmaEquivalence
    open import SigmaPreserves
    open import HLevelLemmas
    calculation : (x : A) → (B x) ≃ fib (pr₁ {A = A}{B}) x
    calculation x =
      begin≃
        B x
          ≃⟨ universal-property-of-identity-type {A = A}{B} x  ⟩
       ∑[ a ∶ A ] (∑[ p ∶ a ≡ x ] B a)
          ≃⟨ sigma-preserves (λ a → left-universal-property-of-idenity-type {A = A}{B} a x) ⟩
       ∑[ a ∶ A ] (∑[ b ∶ B a ] a ≡ x)
         ≃⟨⟩
       ∑[ a ∶ A ] (∑[ b ∶ B a ] (pr₁ {A = A}{B} (a , b) ≡ x) )
         ≃⟨  ∑-assoc ⟩
       (∑[ p ∶ ∑ A B ] (pr₁ p ≡ x))
          ≃⟨⟩
       fib (pr₁ {A = A}{B}) x
        ≃∎

  happly : ∀ {ℓ₁ ℓ₂ : Level} {A : Type ℓ₁}{B : A → Type ℓ₂}
    → {f g : ∏ A B}
    → (f ≡ g)
    → (x : A) →  (f x ≡ g x)
  happly idp x = idp

  weak-extensionality pi-is-contr
    : {ℓ₁ ℓ₂ : Level} {A : Type ℓ₁}{B : A → Type ℓ₂}
    →  ((x : A) → isContr (B x)) → isContr (Π A B)
  weak-extensionality {ℓ₁}{ℓ₂}{A}{B} Bx-is-contr
   = retract-of-singleton Π-is-retract fib-α-id-is-contr
    where
    open import SectionsAndRetractions

    α≃ : ((↑ ℓ₂ A) → ∑ (↑ ℓ₂ A) λ { (Lift a) → B a}) ≃ ((↑ ℓ₂ A) → ↑ ℓ₂ A)
    α≃ = postcomp-≃ (↑ ℓ₂ A)
      (pr₁ , contr-fibers-gives-pr₁-equiv
        (λ { (Lift a) → Bx-is-contr a})) (↑ ℓ₂ A)
    α = α≃ ∙→

    fib-α-id = fib α (id-on (↑ ℓ₂ A))
    fib-α-id-is-contr : isContr (fib-α-id)
    fib-α-id-is-contr = pr₂ α≃ (id-on (↑ ℓ₂ A))

    φ : fib-α-id → Π A B
    φ (g , p) = λ x → tr (λ { (Lift a) → B a}) (happly p (Lift x)) (pr₂ (g (Lift x)))

    ψ : (f : Π A B) → fib-α-id
    ψ f = ((λ {(Lift a) → (Lift a) , f a}) , refl (id-on (↑ ℓ₂ A)))

    Π-is-retract : retract (Π A B) of fib-α-id
    Π-is-retract = (φ , (ψ , λ f → idp))
  pi-is-contr = weak-extensionality

  funext
    : {ℓ₁ ℓ₂ : Level} {A : Type ℓ₁}{B : A → Type ℓ₂}
    → (f g : ∏ A B)
    → (h : ∏[ x ∶ A ] (f x ≡ g x))
    → f ≡ g

  funext {ℓ₁}{ℓ₂}{A}{B} f g h = ap (_!-inv) p
    where
    hat : (∏ A B) → (↑ ℓ₂ A) → ∑ A B
    hat f (Lift a) = (a , f a)

    hat-f≡hat-g : (hat f) ≡ (hat g)
    hat-f≡hat-g = funext' (hat f) (hat g) (λ { (Lift a) → pair= (idp , h a)})

    _! : ∏ A B → ∑[ h ∶ ((↑ ℓ₂ A) → ∑ A B) ] (∏[ x ∶ (↑ ℓ₂ A) ] (π₁ (h x) ≡ lower x) )
    f ! = ( hat f , λ { (Lift a) → refl a})

    _!-inv : ∑[ h ∶ ((↑ ℓ₂ A) → ∑ A B) ] (∏[ x ∶ (↑ ℓ₂ A) ] (π₁ (h x) ≡ (lower x)) ) → ∏ A B
    _!-inv (h , p) = λ x → tr B (p (Lift x)) (π₂ (h (Lift x)))

    -- see that, the round trip gives.
    _ : ((f !) !-inv)  ≡ f
    _ = idp

    p : (f !) ≡ (g !)
    p = pair= (hat-f≡hat-g , q)
      where
      open import HLevelLemmas
      q : PathOver (λ h₁ → ∏ (↑ ℓ₂ A) (λ x → π₁ (h₁ x) ≡ lower x))
                    (π₂ (f !)) hat-f≡hat-g (π₂ (g !))
      q = contr-is-prop  (weak-extensionality (λ {(Lift a) → idp , λ { idp → idp}}))
        (tr (λ h → ∏ (↑ ℓ₂ A) λ x → π₁ (h x) ≡ lower x) hat-f≡hat-g (π₂ (f !))) (π₂ (g !))
    

  fiberwise-transformation fiberwise-map-from_to_
    : ∀ {ℓ₁ ℓ₂ : Level} {A : Type ℓ₁}
    → (P Q : A → Type ℓ₂)
    → Type (ℓ₁ ⊔ ℓ₂)
  fiberwise-transformation P Q = ∏[ x ] (P x → Q x)
  fiberwise-map-from_to_ = fiberwise-transformation

  total
    : ∀ {ℓ₁ ℓ₂ : Level} {A : Type ℓ₁}{P Q : A → Type ℓ₂}
    → (f : fiberwise-map-from P to Q)
    → ((∑ A P) → (∑ A Q))
  total f (a , p) = ( a , f a p)

  fib-total-≃fib-fiberwise
    : ∀ {ℓ₁ ℓ₂ : Level} {A : Type ℓ₁}{P Q : A → Type ℓ₂}
    → (f : fiberwise-map-from P to Q)
    → (x : A) (v : Q x)
    → fib (total f) (( x , v)) ≃ fib (f x) v

  fib-total-≃fib-fiberwise {P = P}{Q} f x v =
    qinv-≃ f' (g' , (λ {(p , idp) → idp}) , λ { (a , idp) → idp})
    where
    private
      f' = λ { ((a , p) , idp) → (p , idp)}
      g' = λ { (p , idp) → ( (x , p) , idp)}

  fib-total-equiv-from-fiberwise-equiv
    :  ∀ {ℓ₁ ℓ₂ : Level} {A : Type ℓ₁}{P Q : A → Type ℓ₂}
    → (f : fiberwise-map-from P to Q)
    → ((x : A) → (f x) is-equiv)  -- this says f is fiberwise equivalence.
    →  ((total f) is-equiv)
  fib-total-equiv-from-fiberwise-equiv f f-fiberwise-equiv
    = λ x → equiv-preserves-contr
                    (≃-sym (fib-total-≃fib-fiberwise f (π₁ x) (π₂ x)))
                    (f-fiberwise-equiv (π₁ x) (π₂ x))

  fib-total-equiv-to-fiberwise-equiv
    :  ∀ {ℓ₁ ℓ₂ : Level} {A : Type ℓ₁}{P Q : A → Type ℓ₂}
    → (f : fiberwise-map-from P to Q)
    → ((total f) is-equiv)
    → ((x : A) → (f x) is-equiv)
  fib-total-equiv-to-fiberwise-equiv f total-is-equiv
    = λ x → λ p → equiv-preserves-contr (fib-total-≃fib-fiberwise f x p) (total-is-equiv ((x , p)))

  happly-is-equiv
    :  ∀ {ℓ₁ ℓ₂ : Level} {A : Type ℓ₁}{B : A → Type ℓ₂}
    → {f g : ∏ A B}
    → (happly {f = f} {g}) is-equiv

  happly-is-equiv {A = A}{B}{f = f}{g} h
    = fib-total-equiv-to-fiberwise-equiv s total-happly-is-equiv g h
    where
    open import SigmaEquivalence
    calculation
      : (∏[ x ∶ A ] (∑[ u ∶ B x ] (f x ≡ u)))
      ≃ (∑[ g ∶ ∏ A B ] (∏[ x ∶ A ] (f x ≡ g x)))
    calculation = choice

    α-codomain-is-contr : isContr ((∑[ g ∶ ∏ A B ] (∏[ x ∶ A ] (f x ≡ g x))))
    α-codomain-is-contr
     = equiv-preserves-contr
         choice
         (pi-is-contr (λ x → pathfrom-is-contr _ _))

    s : (g : (∏ A B)) → (f ≡ g) → (∏[ x ∶ A ] (f x ≡ g x))
    s g p = happly p

    α : (∑[ g ∶ (∏ A B) ] (f ≡ g)) → (∑[ g ∶  ∏ A B ] ∏[ x ∶ A ] (f x ≡ g x))
    α (g , p) = (g , happly p)

    total-happly-is-equiv : α is-equiv
    total-happly-is-equiv (g , p) =
      map-domain-and-codomain-contr-is-equiv
        α-domain-is-contr
        α-codomain-is-contr _ _
      where
      open import SectionsAndRetractions
      α-domain-is-contr : isContr (domain α)
      α-domain-is-contr = pathfrom-is-contr _ _

      map-domain-and-codomain-contr-is-equiv : ∀ {ℓ₁ ℓ₂ : Level}{X : Type ℓ₁}{Y : Type ℓ₂}
        → X is-contr
        → Y is-contr
        → (f : X → Y)
        → f is-equiv
      map-domain-and-codomain-contr-is-equiv {X = X}{Y} X-is-contr Y-is-contr f
        = λ y → ((center-of X-is-contr , contr-is-prop Y-is-contr _ _))
          , λ x → pair= (contr-is-prop X-is-contr _ _ ,
          prop-is-set (contr-is-prop Y-is-contr) _ _ _ _)
