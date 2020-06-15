::

   {-# OPTIONS --without-K --exact-split #-}

   open import BasicTypes public
   open import AlgebraOnPaths public

Transport
---------

::

   transport
     : ∀ {ℓ₁ ℓ₂ : Level} {A : Type ℓ₁}
     → (C : A → Type ℓ₂) {a₁ a₂ : A}
     → (p : a₁ == a₂)
     -------------------------------
     → (C a₁ → C a₂)

   transport C idp = (λ x → x)

More syntax:

::

   tr     = transport
   tr₁    = transport
   transp = transport

Coercion
~~~~~~~~

::

   coe
     : ∀ {ℓ : Level} {A B : Type ℓ}
     → A == B
     ---------
     → (A → B)

   coe p a = transport (λ X → X) p a

and its inverse:

::

   !coe
     : ∀ {ℓ : Level} {A B : Type ℓ}
     → A == B
     ---------
     → (B → A)

   !coe p a = transport (λ X → X) (! p) a

Pathovers
~~~~~~~~~

Let be ``A : Type``, ``a₁, a₂ : A``, ``C : A → Type``, ``c₁ : C a₁`` and
``c₂ : C a₂``. Using the same notation from {% cite hottbook %}, one of
the definitions for the Pathover type is as the shorthand for the path
between the transport along a path ``α : a₁ = a₂`` of the point
``c₁ : C a₁`` and the point ``c₂`` in the fiber ``C a₂``. That is, a
pathover is a term that inhabit the type ``transport C α c₁ = c₂`` also
denoted by ``PathOver C c₁ α c₂``.

::

   PathOver
     : ∀ {ℓ₁ ℓ₂ : Level} {A : Type ℓ₁}
     → (B : A → Type ℓ₂) {a₁ a₂ : A}
     → (b₁ : B a₁) → (α : a₁ == a₂) → (b₂ : B a₂)
     --------------------------------------------
     → Type ℓ₂

   PathOver B b₁ α b₂ = tr B α b₁ == b₂

::

   infix 30 PathOver

   syntax PathOver B b₁ α b₂  = b₁ == b₂ [ B ↓ α ]

Another notation:

::

   ≡Over = PathOver

::

   infix 30 ≡Over
   syntax ≡Over B b α b' = b ≡ b' [ B / α ]

Compositions of Pathovers
~~~~~~~~~~~~~~~~~~~~~~~~~

::

   infixl 80 _·d_
   _·d_
     : ∀ {ℓ₁ ℓ₂ : Level} {A : Type ℓ₁} {B : A → Type ℓ₂}
     → {a₁ a₂ a₃ : A} {p : a₁ ≡ a₂} {q : a₂ ≡ a₃}
     → {b₁ : B a₁}{b₂ : B a₂} {b₃ : B a₃}
     → (b₁ ≡ b₂ [ B / p ])
     → (b₂ ≡ b₃ [ B / q ])
     -------------------------
     → b₁ ≡ b₃ [ B / (p · q) ]

   _·d_ {p = idp} {q = idp} idp idp = idp -- α β = α · β

::

   pathover-comp = _·d_
   _∙d_          = _·d_

::

   tr₁-≡
     : ∀ {ℓ : Level} {A : Type ℓ} {a₀ a₁ a₂ : A}
     → (α : a₁ ≡ a₂)
     → (ε : a₀ ≡ a₁)
     → (δ : a₀ ≡ a₂)
     → (ε ≡ δ [ (λ a' → a₀ ≡ a') / α ])
     ----------------------------------
     → α ≡ ! ε · δ

   tr₁-≡ idp .idp idp idp = idp

Transport along pathovers
~~~~~~~~~~~~~~~~~~~~~~~~~

::

   tr₂
     :  ∀ {ℓ₁ ℓ₂ ℓ₃ : Level} {A : Type ℓ₁} {B : A → Type ℓ₂}
     → (C : (a : A) → (B a → Type ℓ₃))
     → {a₁ a₂ : A}{b₁ : B a₁}{b₂ : B a₂}
     → (p : a₁ == a₂)
     → (q : b₁ == b₂ [ B ↓ p ])
     → C a₁ b₁
     -----------------------
     → C a₂ b₂

   tr₂ C idp idp = id

Gylterud’s tr₂-commute:

::

   tr₂-commute
     : ∀ {ℓ₁ ℓ₂ ℓ₃ : Level} {A : Type ℓ₁} {B : A → Type ℓ₂}
     → (C : (a : A) → (B a → Type ℓ₃))
     → (D : (a : A) → (B a → Type ℓ₃))
     → (f : ∀ a b → C a b → D a b)
     → ∀ {a a' b b'}
     → (p : a ≡ a')
     → (q : b ≡ b' [ B / p ])
     ---------------------------------------------------
     → ∀ c → tr₂ D p q (f a b c) ≡ f a' b' (tr₂ C p q c)

   tr₂-commute C D f idp idp c = idp
