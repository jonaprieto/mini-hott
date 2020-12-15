module Test2 where
   open import MiniHoTT

   A : Set
   A = ℕ


--  a, b : A

  {-
   [ a, b ] : List A
   [ a, b ] := inr ( a , ?)
    -- inr ((a, inr ( b, inl(unit))
    -}

   T : {A : Set} → (X : Set) → Set
   T {A} X = 𝟙 lzero + A × X -- This is an example of a polynomial functor.


   data
     List (A : Set)
      : Set
     where
     [] : List A
     cons : A → List A → List A

   data Vec (A : Set) : ℕ → Set
    where
    nil : ∀ n → Vec A n
    cons : ∀ n → A → Vec A n → Vec A (succ n)

   data Fin : ℕ →  Set
    where
    cero : ∀ {n} → Fin n
    succ : ∀ {n} → Fin n → Fin (succ n)

   at : ∀ {n : ℕ} {A : Set}
    → Vec A (succ n)
    → Fin (succ n)
    → A
   at v n = {!   !}

   go' : ∀ {n} {A : Set}
    → (Fin 0n → A) → Fin n → Vec A n
   go' pick cero     = nil _
   go' pick (succ n) = cons {!   !} (pick {! n  !})
    (go' {! pick    !} {!   !})

   record
     Algebra
      (A : Set)
      (T : Set → Set)
      : Set (lsuc lzero)
     where
     constructor algebra
     field
      X : Set
      μ : T X → X

   -- Objects: (X, μ)
   -- morphisms f : (X, μ) ­--> (Y, ν)
   --   this is given by α : X → Y, that makes the diagram commutes.
   -- Initial object: Object  (X, μ) + initiallity condition:
   --   Any other (Y, ν), there exists unique α : X → Y such that...


   list-is-an-algebra : (A : Set) → Algebra A (λ X → 𝟙 lzero + A × X)
   list-is-an-algebra A =
    algebra (List A) λ { (inl x) → []
                       ; (inr (a , xs)) → cons a xs
                       }




   -- where (T X -> X) is the type of list with elements of type A.
   -- elements? is TA a set?
   -- Yes, assuming A is a set. Let's find that.

   list-of-nats-is-set
     : A is-set
     → isSet (T A)
   list-of-nats-is-set A-is-set
    = +-set
        (prop-is-set 𝟙-is-prop)
        (∑-set
          A-is-set
          λ _ → A-is-set)

  -- T(X) = 1+X + (X ×X) a


