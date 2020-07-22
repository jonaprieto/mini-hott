Taken  from:
https://www.cs.bham.ac.uk/~mhe/agda-new/UF-Retracts.html#193

::
    {-# OPTIONS --without-K --exact-split #-}

    open import BasicFunctions
    open import TransportLemmas
    open import EquivalenceType
    open import QuasiinverseType
    open import QuasiinverseLemmas
    open import HLevelTypes
    open import UnivalenceAxiom
    open import CoproductIdentities
    open import TypesofMorphisms
    open import HomotopyType

    module SectionsAndRetractions where

    has-section : {ℓ₁ ℓ₂ : Level} {X : Type ℓ₁} {Y : Type ℓ₂} → (X → Y) → Type _
    has-section r = ∑[ s ] (r ∘ s ∼ id {A = codomain r})

    is-section : {ℓ₁ ℓ₂ : Level} {X : Type ℓ₁} {Y : Type ℓ₂ } → (X → Y) → Type _
    is-section s = ∑[ r ] (r ∘ s ∼ id)

    sections-are-lc : {ℓ₁ ℓ₂ : Level} {X : Type ℓ₁} {Y : Type ℓ₂ } (s : X → Y)
                    → is-section s → s is-injective
    sections-are-lc s (r , rs) {x} {x'} p = ! (rs x) · ap r p · rs x'

    retract_of_ : {ℓ₁ ℓ₂ : Level} → Type ℓ₁ → Type ℓ₂ → Type _
    retract Y of X = ∑[ r ∶ (X → Y) ] has-section r

    retract-of-singleton
      : {ℓ₁ ℓ₂ : Level} {X : Type ℓ₁} {Y : Type ℓ₂ }
      → retract Y of X
      → is-singleton X
      → is-singleton Y
    retract-of-singleton (r , s , rs) (c , φ) = r c , λ y → ap r (φ (s y)) · rs y


