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

     pair-≃-∑
        : ∀ {l1 l2 : Level}{A : Type l1}{B : A → Type l2}
        → {v w : ∑ A B}
        → (v ≡ w) ≃ (∑[ α ∶ π₁ v ≡ π₁ w ] (tr B α (π₂ v) ≡ (π₂ w)))
     pair-≃-∑ = qinv-≃ Σ-componentwise (Σ-bycomponents
              , (λ { (idp , idp) → idp}) , λ {idp → idp})

::

     tuples-assoc
        : {ℓ1 ℓ2 ℓ3 : Level}
        → {A : Type ℓ1}
        → {B : A → Type ℓ2}
        → {C : (a : A) → B a → Type ℓ3}
        → {u₁ u₂ : A} {v₁ : B u₁}{v₂ : B u₂} {c₁ : C u₁ v₁}{c₂ : C u₂ v₂}
        → (u₁ , v₁ , c₁) ≡ (u₂ , v₂ , c₂)
        ≃ ((u₁ , v₁) , c₁) ≡ ((u₂ , v₂) , c₂)
     tuples-assoc = qinv-≃ (λ {idp → idp}) ( (λ {idp → idp}) , (λ {idp → idp}) , (λ {idp → idp}))

     ∑-assoc
        : {ℓ1 ℓ2 ℓ3 : Level}
        → {A : Type ℓ1}
        → {B : A → Type ℓ2}
        → {C : (a : A) → B a → Type ℓ3}
        → (∑[ a ∶ A ] (∑[ b ∶ B a ] C a b))
        ≃ (∑[ ab ∶ ∑ A B ] (C (fst ab) (snd ab)))
     ∑-assoc = qinv-≃ f
        (g , (λ { _ → idp}) , λ {_ → idp})
        where
        private
          f = λ {(a , (b , c)) → ( (a , b) , c)}
          g = λ {((a , b) , c) → (a , (b , c))}

     ∑-assoc'
        : {ℓ1 ℓ2 ℓ3 : Level}
        → {A : Type ℓ1}
        → {B : A → Type ℓ2}
        → {C : ∑ A B → Type ℓ3}
        → (∑[ ab ∶ ∑ A B ] (C ab))
        ≃ (∑[ a ∶ A ] (∑[ b ∶ B a ] C (a , b)))

     ∑-assoc' = qinv-≃ g
        (f ,  (λ {_ → idp} ) , λ {_ → idp} )
        where
        private
          f = λ {(a , (b , c)) → ( (a , b) , c)}
          g = λ {((a , b) , c) → (a , (b , c))}

     module _ {ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level}
        where

        ∑-comm₂
          : (A : Type ℓ₁)
          → (B : A → Type ℓ₂)
          → (C : A → Type ℓ₃)
          → (D : (ab : ∑[ ab ∶ ∑ A B ] (C (π₁ ab))) → Type ℓ₄)
          → (∑[ ab ∶ ∑ A B ] ∑[ c ∶ C (π₁ ab) ] D (ab , c))
          ≃ (∑[ ac ∶ ∑ A C ] ∑[ b ∶ B (π₁ ac) ] D (( (π₁ ac , b) , π₂ ac)))
        ∑-comm₂ A B C D = qinv-≃ f (g , ((λ {_ → idp}) , λ _ → idp))
          where
          private
            f = λ { ((a , b) , (c , d)) → (( a , c) , (b , d))}
            g = λ { ((a , c) , (b , d)) → ((a , b) , (c , d))}

::

     choice
        : {ℓ1 ℓ2 ℓ3 : Level}
        → {A : Type ℓ1}
        → {B : A → Type ℓ2}
        → {C : (a : A) → B a → Type ℓ3}
        → Π A (λ a → Σ (B a) (λ b → C a b)) ≃ Σ (Π A B) (λ g → Π A (λ a → C a (g a)))

     choice = qinv-≃ f (g , (λ _ → idp) , (λ _ → idp))
       where f = λ c → ((λ a → fst (c a)) , (λ a → snd (c a)))
             g = λ d → (λ a → (fst d a , snd d a))
