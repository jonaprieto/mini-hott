::

   {-# OPTIONS --without-K --exact-split #-}
   open import Intro public

Types
=====

Empty type
----------

A type without points is the *empty* type (also called falsehood).

.. raw:: html

   <!-- tabs:start -->

\*\* Declaration \*\*
^^^^^^^^^^^^^^^^^^^^^

::

   data
     𝟘 (ℓ : Level)
       : Type ℓ
     where

\*\* Additionally syntax \*\*
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

::

   ⊥     = 𝟘
   Empty = 𝟘

.. raw:: html

   <!-- tabs:end -->

.. raw:: html

   <!-- tabs:start -->

\*\* Elimination principle \*\*
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

*Ex falso quodlibet*:

::

   exfalso
     : ∀ {ℓ₁ ℓ₂ : Level} {A : Type ℓ₁}
     ------------
     → (⊥ ℓ₂ → A)

   exfalso ()

.. _additionally-syntax-1:

\*\* Additionally syntax \*\*
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

::

   Empty-elim = exfalso
   ⊥-elim     = exfalso
   𝟘-elim     = exfalso

.. raw:: html

   <!-- tabs:end -->

We abbreviate functions with codomain the empty type by using the prefix
symbol of the negation.

::

   ¬ : ∀ {ℓ : Level} → Type ℓ → Type ℓ
   ¬ {ℓ} A = (A → ⊥ ℓ)

Unit type
---------

Consequently, we now consider the type with one point (also called
*unit* type). This type is defined in Agda as a record, this because of
the :math:`η`-rule definitionally we get.

.. raw:: html

   <!-- tabs:start -->

.. _declaration-1:

\*\* Declaration \*\*
^^^^^^^^^^^^^^^^^^^^^

::

   record
     𝟙 (ℓ : Level)
       : Type ℓ
     where
     constructor unit

.. _additionally-syntax-2:

\*\* Additionally syntax \*\*
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

For this type:

::

   Unit = 𝟙
   ⊤    = 𝟙

For the data constructor:

::

   pattern ★ = unit
   pattern ∗ = unit

.. raw:: html

   <!-- tabs:end -->

.. raw:: html

   <!-- tabs:start -->

.. _elimination-principle-1:

\*\* Elimination principle \*\*
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

::

   unit-elim
     : ∀ {ℓ₁ ℓ₂ : Level} {A : Type ℓ₂}
     → (a : A)
     ------------
     → (𝟙 ℓ₁  → A)
   unit-elim a ∗ = a

.. raw:: html

   <!-- tabs:end -->

Two-point type
--------------

.. raw:: html

   <!-- tabs:start -->

.. _declaration-2:

\*\* Declaration \*\*
^^^^^^^^^^^^^^^^^^^^^

::

   data
     𝟚 (ℓ : Level)
       : Type (lsuc ℓ)
     where
     𝟘₂ : 𝟚 ℓ
     𝟙₂ : 𝟚 ℓ

.. _additionally-syntax-3:

\*\* Additionally syntax \*\*
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

::

   Bool = 𝟚 lzero

Constructors synonyms:

::

   false : 𝟚 lzero
   false = 𝟘₂

   true : 𝟚 lzero
   true  = 𝟙₂

   ff = false
   tt = true

.. raw:: html

   <!-- tabs:end -->

Natural numbers
---------------

.. raw:: html

   <!-- tabs:start -->

.. _declaration-3:

\*\* Declaration \*\*
^^^^^^^^^^^^^^^^^^^^^

::

   data
     ℕ : Type lzero
     where
     zero : ℕ
     succ : ℕ → ℕ

   {-# BUILTIN NATURAL ℕ #-}

.. _additionally-syntax-4:

\*\* Additionally syntax \*\*
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

::

   Nat = ℕ

\*\* An order relation \*\*
^^^^^^^^^^^^^^^^^^^^^^^^^^^

::

   module ℕ-ordering (ℓ : Level) where
     _<_ : ℕ → ℕ → Type ℓ
     zero   < zero   = ⊥ _
     zero   < succ b = ⊤ _
     succ _ < zero   = ⊥ _
     succ a < succ b = a < b

::

     _>_ : ℕ → ℕ → Type ℓ
     a > b = b < a

.. raw:: html

   <!-- tabs:end -->

.. _types-1:

∑-types
-------

Dependent sum type is a type of pairs where the second term may depend
on the first.

.. raw:: html

   <!-- tabs:start -->

.. _declaration-4:

\*\* Declaration \*\*
^^^^^^^^^^^^^^^^^^^^^

::

   record
     ∑ {ℓ₁ ℓ₂ : Level}
      (A : Type ℓ₁) (B : A → Type ℓ₂)
      -------------------------------
      : Type (ℓ₁ ⊔ ℓ₂)
     where
     constructor _,_
     field
       π₁ : A
       π₂ : B π₁

   infixr 60 _,_
   open ∑ public

   {-# BUILTIN SIGMA ∑ #-}

.. _additionally-syntax-5:

\*\* Additionally syntax \*\*
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

::

   Σ = ∑ -- \Sigma and \sum

   syntax ∑ A (λ a → B) = ∑[ a ∶ A ] B

   Σ-s0 : ∀ {ℓ₁ ℓ₂} (A : Type ℓ₁) → (A → Type ℓ₂) → Type (ℓ₁ ⊔ ℓ₂)
   Σ-s0 A = Σ _
   syntax Σ-s0 A (λ x → B) = Σ[ x ∶ A ] B

   Σ-s1 : ∀ {ℓ₁ ℓ₂} {A : Type ℓ₁} → (A → Type ℓ₂) → Type (ℓ₁ ⊔ ℓ₂)
   Σ-s1 = Σ _
   syntax Σ-s1 (λ x → B) = ∑[ x ] B

   Σ-s2 : ∀ {ℓ₁ ℓ₂} {A : Type ℓ₁} → (A → Type ℓ₂) → Type (ℓ₁ ⊔ ℓ₂)
   Σ-s2 = Σ _
   syntax Σ-s2 (λ x → B) = Σ[ x ] B

Constructor synonyms:

::

   proj₁ = π₁
   proj₂ = π₂

   pr₁   = π₁
   pr₂   = π₂

   fst   = π₁
   snd   = π₂

   #     =  π₁

.. raw:: html

   <!-- tabs:end -->

We use the built-in Σ-type in Agda, thus, we “pattern match” instead of
declaring a elimination principle for it.

Π-types
-------

In dependent type theories, the notion of a function is extended by the
notion of a *dependent* function. These are those functions where the
codomain may dependent on values of its domain.

.. raw:: html

   <!-- tabs:start -->

.. _declaration-5:

\*\* Declaration \*\*
^^^^^^^^^^^^^^^^^^^^^

::

   ∏
     : ∀ {ℓ₁ ℓ₂ : Level}
     → (A : Type ℓ₁) (B : A → Type ℓ₂)
     ---------------------------------
     → Type (ℓ₁ ⊔ ℓ₂)

   ∏ A B = (x : A) → B x

.. _additionally-syntax-6:

\*\* Additionally syntax \*\*
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

::

   -- \prod vs \Pi
   Π = ∏

   syntax ∏ A (λ a → B) = ∏[ a ∶ A ] B

   ∏-s0 : ∀ {ℓ₁ ℓ₂} (A : Type ℓ₁) → (A → Type ℓ₂) → Type (ℓ₁ ⊔ ℓ₂)
   ∏-s0 A = ∏ _
   syntax ∏-s0 A (λ x → B) = Π[ x ∶ A ] B

   ∏-s1 : ∀ {ℓ₁ ℓ₂} {A : Type ℓ₁} → (A → Type ℓ₂) → Type (ℓ₁ ⊔ ℓ₂)
   ∏-s1 = ∏ _
   syntax ∏-s1 (λ x → B) = ∏[ x ] B

   ∏-s2 : ∀ {ℓ₁ ℓ₂} {A : Type ℓ₁} → (A → Type ℓ₂) → Type (ℓ₁ ⊔ ℓ₂)
   ∏-s2 = ∏ _
   syntax ∏-s2 (λ x → B) = Π[ x ] B

.. raw:: html

   <!-- tabs:end -->

Products
--------

A particular case of Σ-types is the type of *products*. A product of two
types :math:`A` and :math:`B` is the collection of pairs between an
element of type :math:`A` with one of type :math:`B`. However, there is
no relation between those two.

.. raw:: html

   <!-- tabs:start -->

.. _declaration-6:

\*\* Declaration \*\*
^^^^^^^^^^^^^^^^^^^^^

::

   _×_
     : ∀ {ℓ₁ ℓ₂ : Level}
     → (A : Type ℓ₁) (B : Type ℓ₂)
     -----------------------------
     → Type (ℓ₁ ⊔ ℓ₂)

   A × B = ∑ A (λ _ → B)

   infixl  39 _×_

.. raw:: html

   <!-- tabs:end -->

Coproducts
----------

A coproduct between types :math:`A` and :math:`B` (also called sum
types) is a type of their *disjoint union*, i.e., this type is formed by
tagging which elements comes from the type :math:`A` and :math:`B`. The
tags are the constructor for this type, named here as ``inr`` or
``inl``, that stands for right and left injection, respectively.

.. raw:: html

   <!-- tabs:start -->

.. _declaration-7:

\*\* Declaration \*\*
^^^^^^^^^^^^^^^^^^^^^

::

   data
     _+_ {ℓ₁ ℓ₂ : Level} (A : Type ℓ₁)(B : Type ℓ₂)
       : Type (ℓ₁ ⊔ ℓ₂)
     where
     inl : A → A + B
     inr : B → A + B

   infixr 31 _+_

.. raw:: html

   <!-- tabs:end -->

.. raw:: html

   <!-- tabs:start -->

.. _elimination-principle-2:

\*\* Elimination principle \*\*
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

::

   +-elim
     : ∀ {ℓ₁ ℓ₂ ℓ₃ : Level}
     → {A : Type ℓ₁}{B : Type ℓ₂} {C : Type ℓ₃}
     → (A → C) → (B → C)
     -------------------
     → (A + B) → C

   +-elim A→C _  (inl x) = A→C x
   +-elim _  B→C (inr x) = B→C x

.. _additionally-syntax-7:

\*\* Additionally syntax \*\*
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

::

   cases = +-elim

   syntax cases f g = ⟨ f + g ⟩

.. raw:: html

   <!-- tabs:end -->

Finite sets
-----------

Among the diffrent way, one can define *finite* types, We opt to use two
version, the first version is a ∑-type while the second one is a sum
type. Each definition offers its own advantages and drawbacks. The
former is much clear while the latter is more practical.

A *finite type* of :math:`n : \mathsf{N}` elements is of type
:math:`\mathsf{Fin}_{n}`. This type is the collection of natural numbers
strictly less than :math:`n`. We will prove later on that, indeed, these
finite types are sets, and any finite type is equivalent to some
:math:`n`-finite type.

.. raw:: html

   <!-- tabs:start -->

.. _declaration-8:

\*\* Declaration \*\*
^^^^^^^^^^^^^^^^^^^^^

::

   Fin : ∀ {ℓ : Level} → ℕ → Type ℓ
   Fin {ℓ} n = Σ ℕ (λ m → m < n)
     where open ℕ-ordering ℓ

.. _additionally-syntax-8:

\*\* Additionally syntax \*\*
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

::

   syntax Fin n = ⟦ n ⟧

\*\* The function bound-of \*\*
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

::

   bound-of : ∀ {ℓ : Level} {n : ℕ} → Fin {ℓ} n → ℕ
   bound-of {n = n} _ = n

.. raw:: html

   <!-- tabs:end -->

Another definition for finite sets we use is the following.

.. raw:: html

   <!-- tabs:start -->

\*\* Alternative Declaration \*\*
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

::

   module _ {ℓ : Level}  where

     ⟦_⟧₂ : ℕ → Type ℓ
     ⟦_⟧₂ zero      = 𝟘 _
     ⟦_⟧₂ (succ n)  = 𝟙 ℓ + ⟦ n ⟧₂

\*\* Alternative fin-succ \*\*
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

::

     ⟦⟧₂-succ
       : {n : ℕ}
       → ⟦ n ⟧₂ → ⟦ succ n ⟧₂

     ⟦⟧₂-succ {succ n} (inl x) = inr (inl unit)
     ⟦⟧₂-succ {succ n} (inr x) = inr (⟦⟧₂-succ x)

\*\* Alternative fin-pred \*\*
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

::

     ⟦⟧₂-pred
       : ∀ (n : ℕ)
       → ⟦ n ⟧₂ → ⟦ n ⟧₂

     ⟦⟧₂-pred (succ n) (inl x) = inl x
     ⟦⟧₂-pred (succ n) (inr x) = inr (⟦⟧₂-pred n x)

.. raw:: html

   <!-- tabs:end -->

Equalities
----------

In HoTT, we have a different interpretation of type theory in which the
set-theoretical notion of *sets* for *types* is replaced by the
topological notion of *spaces*.

The (homogeneous) equality type also called identity type is considered
a primary type (included in the theory by default). We denote the
identity type between :math:`a,b : A` as :math:`a =_{A} b` (also denoted
by :math:`\mathsf{Id}_{A}(a, b)` or :math:`a⇝b`. For the identity type,
there is only one constructor, one way to inhabit such types. This is
the reflexivity path (also called :math:`\mathsf{idp}` or
:math:`\mathsf{refl}`).

.. raw:: html

   <!-- tabs:start -->

\*\* Declariton \*\*
^^^^^^^^^^^^^^^^^^^^

::

   data
     _==_ {ℓ : Level}{A : Type ℓ} (a : A)
       : A → Type ℓ
     where
     idp : a == a

   {-# BUILTIN EQUALITY _==_  #-}

.. _additionally-syntax-9:

\*\* Additionally syntax \*\*
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

::

   Eq   = _==_
   Id   = _==_
   Path = _==_
   _⇝_  = _==_   -- type this '\r~'
   _≡_  = _==_

   infix 30 _==_ _⇝_ _≡_

   _≠_ : ∀ {ℓ : Level}{A : Type ℓ}(x y : A) → Type ℓ
   x ≠ y = ¬ (x == y)

.. raw:: html

   <!-- tabs:end -->

.. raw:: html

   <!-- tabs:start -->

\*\* Reflexivity path of a given point \*\*
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

::

   refl
     : ∀ {ℓ : Level} {A : Type ℓ}
     → (a : A)
     ---------
     → a == a

   refl  a = idp

\*\* Symmetry of a path \*\*
^^^^^^^^^^^^^^^^^^^^^^^^^^^^

::

   sym
     : ∀ {ℓ : Level} {A : Type ℓ} {x y : A}
     → x == y
     --------
     → y == x

   sym idp = idp

   syntax sym p = − p

.. raw:: html

   <!-- tabs:end -->

To work with identity types, the induction principle is the
J-eliminator.

*Paulin-Mohring J rule*

.. raw:: html

   <!-- tabs:start -->

\*\* Path-induction v1 \*\*
^^^^^^^^^^^^^^^^^^^^^^^^^^^

::

   J
     : ∀ {ℓ : Level} {A : Type ℓ} {a : A} {ℓ₂ : Level}
     → (B : (a' : A) (p : a == a') → Type ℓ₂)
     → (B a idp)
     ----------------------------------------
     → ({a' : A} (p : a == a') → B a' p)

   J _ b idp = b

.. raw:: html

   <!-- tabs:end -->

Other custom types
==================

Implications
------------

::

   data
     _⇒_ {ℓ₁ ℓ₂ : Level}
       (A : Type ℓ₁) (B : Type ℓ₂)
       ---------------------------
       : Type (ℓ₁ ⊔ ℓ₂)
     where
     fun : (A → B) → A ⇒ B

Bi-implications
---------------

::

   _⇔_
     : ∀ {ℓ₁ ℓ₂}
     → Type ℓ₁ → Type ℓ₂
     -------------------
     → Type (ℓ₁ ⊔ ℓ₂)

   A ⇔ B = (A → B) × (B → A)

More syntax:

::

   _↔_ = _⇔_

   infix 30 _↔_ _⇔_

Decidable type
--------------

::

   data
     Dec {ℓ : Level}(P : Type ℓ)
       : Type ℓ
     where
     yes : ( p : P) → Dec P
     no  : (¬p : P → ⊥ ℓ) → Dec P

::

   ⌊_⌋ : ∀ {ℓ : Level}{P : Type ℓ} → Dec P → 𝟚 ℓ
   ⌊ yes _ ⌋ = 𝟙₂
   ⌊ no  _ ⌋ = 𝟘₂


::

   Decidable
     : ∀ {ℓ₁ ℓ₂ ℓ : Level} {A : Type ℓ₁}{B : Type ℓ₂}
     → (A → B → Type ℓ)
     → Type (ℓ₁ ⊔ ℓ₂ ⊔ ℓ)

   Decidable _∼_ = ∀ x y → Dec (x ∼ y)

Heterogeneous equality
----------------------

::

   data
     ≡≡ {ℓ : Level} (A : Type ℓ)
       : (B : Type ℓ)
       → (α : A == B) (a : A) (b : B)
       → Type (lsuc ℓ)
     where
     idp : {a : A} → ≡≡ A A idp a a
