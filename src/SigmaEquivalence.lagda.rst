Sigma equivalences
-------------------------------------

::

   {-# OPTIONS --without-K --exact-split #-}
   open import TransportLemmas
   open import EquivalenceType

   open import HomotopyType
   open import QuasiinverseType

   open import CoproductIdentities

::

   module SigmaEquivalence where

::

     module _ {ℓ₁ ℓ₂ : Level} (A : Type ℓ₁) (P : A → Type ℓ₂) where

::

       pair=Equiv
         : {v w : Σ A P}
         --------------------------------------------------------------------
         → Σ (π₁ v == π₁ w) (λ p → tr (λ a → P a) p (π₂ v) == π₂ w) ≃ (v == w)

       pair=Equiv = qinv-≃ Σ-bycomponents (Σ-componentwise , HΣ₁ , HΣ₂)
         where
           HΣ₁ : Σ-bycomponents ∘ Σ-componentwise ∼ id
           HΣ₁ idp = idp

           HΣ₂ : Σ-componentwise ∘ Σ-bycomponents ∼ id
           HΣ₂ (idp , idp) = idp

       private
         f : {a₁ a₂ : A} {α : a₁ == a₂}{c₁ : P a₁} {c₂ : P a₂}
           → {β : a₁ == a₂}
           → {γ : transport P β c₁ == c₂}
           → ap π₁ (pair= (β , γ)) == α → β == α
         f {β = idp} {γ = idp} idp = idp

         g : {a₁ a₂ : A} {α : a₁ == a₂}{c₁ : P a₁} {c₂ : P a₂}
           → {β : a₁ == a₂}
           → {γ : transport P β c₁ == c₂}
           → β == α → ap π₁ (pair= (β , γ)) == α
         g {β = idp} {γ = idp} idp = idp

         f-g : {a₁ a₂ : A} {α : a₁ == a₂}{c₁ : P a₁} {c₂ : P a₂}
           → {β : a₁ == a₂}
           → {γ : transport P β c₁ == c₂}
           → f {α = α}{β = β}{γ} ∘ g {α = α}{β = β} ∼ id
         f-g {β = idp} {γ = idp} idp = idp

         g-f : {a₁ a₂ : A} {α : a₁ == a₂}{c₁ : P a₁} {c₂ : P a₂}
           → {β : a₁ == a₂}
           → {γ : transport P β c₁ == c₂}
           → g {α = α}{β = β}{γ} ∘ f {α = α}{β = β}{γ} ∼ id
         g-f {β = idp} {γ = idp} idp = idp

::

       ap-π₁-pair=Equiv
         : ∀ {a₁ a₂ : A} {c₁ : P a₁} {c₂ : P a₂}
         → (α : a₁ == a₂)
         → (γ : Σ (a₁ == a₂) (λ p → c₁ == c₂ [ P ↓ p ]))
         -----------------------------------------------
         → (ap π₁ (pair= γ) == α) ≃ (π₁ γ == α)

       ap-π₁-pair=Equiv {a₁ = a₁} α (β , γ) = qinv-≃ f (g , f-g , g-f)

::

     postulate
       ∑-≃-∑-with-≃
         : ∀ {ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level}{A : Type ℓ₁}{B : A → Type ℓ₂}{A' : Type ℓ₃}{B' : A' → Type ℓ₄}
          → (e : A ≃ A')
          → ∑ A B ≃ ∑ A' B'

::

     postulate
       ∑-≃-∑-with-→
         : ∀ {ℓ₁ ℓ₂ ℓ₃ ℓ₄}{A : Type ℓ₁}{B : A → Type ℓ₂}{A' : Type ℓ₃}{B' : A' → Type ℓ₄}
          → (f : A → A')
          → (α : (a : A) → B a → B' (f a))
          -- Then if
          → isEquiv f
          → (a : A) → isEquiv (α a)
          -------------------------------------------
          → isEquiv (∑-map {B = B}{B' = B'} f α)
