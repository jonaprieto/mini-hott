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

     coe-ua
       : ∀ {ℓ : Level} {A B : Type ℓ}
       → (α : A ≃ B)
       -------------------------------------
       → (∀ x → (coe (ua α) x) == ((α ∙) x))

     coe-ua α = happly (ap (lemap) (ua-β α))

::

     coe-ua-·
       : ∀ {ℓ : Level} {A B C : Type ℓ}
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

In addition, we can state a similar result with ``idtoequiv``:

::

     idtoequiv-ua-·
       : ∀ {ℓ : Level} {A B C : Type ℓ}
       → (α : A ≃ B)
       → (β : B ≃ C)
       ---------------------------------------------------
       → ite (ua α · ua β) ≡ ((ite (ua α)) :>≃ (ite (ua β)))

     idtoequiv-ua-· α β = sameEqv (coe-ua-· α β)
       where open import HLevelLemmas

     ite-ua-· = idtoequiv-ua-·

::

     postulate
      :>≃-ite-ua
       : ∀ {ℓ : Level} {A B C : Type ℓ}
       → (α : A ≃ B)    → (β : B ≃ C)
       ------------------------------
       → (α :>≃ β) ≡ ite (ua α · ua β)

     {- -- below is the proof, but it blows up the time of type-checking.
       lemma α β =
           begin
             (α :>≃ β)
               ≡⟨ ap₂ (λ x y → x :>≃ y) (! (ua-β α)) (! (ua-β β)) ⟩
             (ite (ua α)) :>≃ (ite (ua β))
               ≡⟨ ! (ite-ua-· α β) ⟩
             ite (ua α · ua β)
     -}
