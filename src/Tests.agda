
module Tests where
  open import BasicFunctions

  open import TransportLemmas
  open import EquivalenceType

  open import HomotopyType
  open import HomotopyLemmas

  open import HalfAdjointType
  open import QuasiinverseType
  open import QuasiinverseLemmas
  open import HLevelTypes
  open import HLevelLemmas
  open import TruncationType
  open import UnivalenceAxiom
  open import FunExtAxiom

  module _
    {ℓ : Level} {A B : Type ℓ}
    where

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
        cβ : π₁ (α :>≃ β) == π₁ (α :>≃ idtoeqv (ua β))
        cβ = ap (λ w → π₁ (α :>≃ w)) (! ua-β β)

        cα : π₁ (α :>≃ idtoeqv (ua β)) ≡ π₁ (idtoeqv (ua α) :>≃ idtoeqv (ua β))
        cα = ap (λ w → π₁ (w :>≃ idtoeqv (ua β))) (! ua-β α)