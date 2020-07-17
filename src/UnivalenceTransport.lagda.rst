Transport and Univalence
------------------------

::

   {-# OPTIONS --without-K --exact-split #-}
   open import TransportLemmas
   open import EquivalenceType

   open import HomotopyType
   open import FunExtAxiom
   open import QuasiinverseType
   open import QuasiinverseLemmas

   open import UnivalenceAxiom

   module UnivalenceTransport where

::

     transport-family-ap
       : ∀ {ℓ₁ ℓ₂ : Level} {A : Type ℓ₁}
       → (B : A → Type ℓ₂)
       → {x y : A}
       → (p : x == y)
       → (u : B x)
       ---------------------------------------------------
       → transport B p u == transport (λ X → X) (ap B p) u

     transport-family-ap B idp u = idp

::

     transport-family-idtoeqv
       : ∀ {ℓ₁ ℓ₂ : Level} {A : Type ℓ₁}
       → (B : A → Type ℓ₂)
       → {x y : A}
       → (p : x == y)
       → (u : B x)
       ----------------------------------------------
       → transport B p u == fun≃ (idtoeqv (ap B p)) u

     transport-family-idtoeqv B idp u = idp

::


     transport-ua
          : ∀ {ℓ₁ ℓ₂ : Level} {A : Type ℓ₁}
          → (B : A → Type ℓ₂)
          → {x y : A}
          → (p : x == y)
          → (e : B x ≃ B y)
          → ap B p == ua e
          -----------------
          → (u : B x) → transport B p u == (fun≃ e) u

     transport-ua B idp e q u =
          begin
            transport B idp u
              ==⟨ transport-family-idtoeqv B idp u ⟩
            fun≃ (idtoeqv (ap B idp)) u
              ==⟨ ap (λ r → fun≃ (idtoeqv r) u) q ⟩
            fun≃ (idtoeqv (ua e)) u
              ==⟨ ap (λ r → fun≃ r u) (ua-β e) ⟩
            fun≃ e u
          ∎

::

     funext-transport-ua
        : ∀ {ℓ₁ ℓ₂ : Level} {A : Type ℓ₁}
        → (B : A → Type ℓ₂)
        → {x y : A}
        → (p : x == y)
        → (e : B x ≃ B y)
        → ap B p == ua e
        -----------------
        → transport B p == (fun≃ e)

     funext-transport-ua B p e x₁ = funext (transport-ua B p e x₁)

::

     module _
      {ℓ : Level} {A B : Type ℓ}
      where
      abstract
        coe-ua
          : (α : A ≃ B)
          -------------------------------------
          → (∀ x → (coe (ua α) x) == ((α ∙) x))

        coe-ua α = happly (ap (lemap) (ua-β α))

        coe-ua-·
          : {C : Type ℓ}
          → (α : A ≃ B)
          → (β : B ≃ C)
          --------------------------------------------------
          → coe (ua α · ua β) ≡ ((coe (ua α)) :> coe (ua β))

        coe-ua-· α β =
            begin
              coe (ua α · ua β)
                ≡⟨⟩
              tr (λ X → X) (ua α · ua β)
                ≡⟨ ! (transport-comp (ua α) (ua β)) ⟩
              (tr (λ X → X) (ua α)) :> (tr (λ X → X) (ua β))
                ≡⟨ idp ⟩
              ((coe (ua α)) :> coe (ua β))
            ∎

        idtoequiv-ua-· ite-ua-·
          : {C : Type ℓ}
          → (α : A ≃ B)
          → (β : B ≃ C)
          ---------------------------------------------------
          → idtoeqv (ua α · ua β) ≡ ((idtoeqv (ua α)) :>≃ (idtoeqv (ua β)))

        idtoequiv-ua-· α β = sameEqv (coe-ua-· α β)
            where open import HLevelLemmas
        ite-ua-· = idtoequiv-ua-·

        :>≃-ite-ua
          : {C : Type ℓ}
          → (α : A ≃ B)  → (β : B ≃ C)
          ------------------------------
          → (α :>≃ β) ≡ idtoeqv (ua α · ua β)

        :>≃-ite-ua {C = C} α β =
          begin
            (α :>≃ β)
              ≡⟨ sameEqv cβ ⟩
            (α :>≃ (idtoeqv (ua β)))
              ≡⟨ sameEqv cα ⟩
            (idtoeqv {A = A} (ua {A = A} α)) :>≃ (idtoeqv (ua β))
              ≡⟨ ! ite-ua-· {C = C} α β ⟩
            idtoeqv (ua α · ua β)
            ∎
            where
            open import HLevelLemmas

            cβ : π₁ (α :>≃ β) == π₁ (α :>≃ idtoeqv (ua β))
            cβ = ap (λ w → π₁ (α :>≃ w)) (! ua-β β)

            cα : π₁ (α :>≃ idtoeqv (ua β)) ≡ π₁ (idtoeqv (ua α) :>≃ idtoeqv (ua β))
            cα = ap (λ w → π₁ (w :>≃ idtoeqv (ua β))) (! ua-β α)

