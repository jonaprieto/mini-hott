Quick start
-----------

This documentation is generated automatically. The sub-folder ``src`` in
the repository of this project contains the Agda sources.

Code conventions
~~~~~~~~~~~~~~~~

Definitions and theorems are typed with unicode characters. Lemmas and
theorems are shown as rule inferences as much as possible. Level
universes are explicitly given.

.. raw:: html

   <pre>
   termName
     :  ∀ {ℓ₁ ℓ₂.. : Level} {A : Type ℓ₁}   -- Implicit assumptions
     → (B : A → Type ℓ₂)                    -- Explicit assumptions
     → ...                                  -- (Most relevant) premises
     ---------------------
     → ...                                  -- Conclusion
   </pre>

.. raw:: html

   <pre>
   termName = definition
     where
     helper1 : ...
     helper2 = def...
   </pre>

Proof relevancy
~~~~~~~~~~~~~~~

To be consistent with univalent type theory, we tell Agda to not use
*Axiom K* for type-checking by using the option ``without-K`` on the top
of the files.

::

   {-# OPTIONS --without-K #-}

In addition, without the Axiom K, Agda’s ``Set`` is not a good name for
universes in HoTT. So, we rename ``Set`` to ``Type``. Our type judgments
then will include the universe level as one explicit argument. Also, we
want to have judgmental equalities for each usage of (=) so we use the
following option.

::

   {-# OPTIONS --exact-split #-}

::

   open import Agda.Primitive
     using ( Level ; lsuc; lzero; _⊔_ ) public

Note that ``l ⊔ q`` is the maximum of two hierarchy levels ``l`` and
``q`` and we use this later on to define types in full generality.

::

   Type
     : (ℓ : Level)
     → Set (lsuc ℓ)

   Type ℓ = Set ℓ

::

   Type₀
     : Type (lsuc lzero)

   Type₀ = Type lzero

::

   Type₁
     : Type (lsuc (lsuc lzero))

   Type₁ = Type (lsuc lzero)

The following type is to lift a type to a higher universe.

::

   record
     ↑ {a : Level} ℓ (A : Type a)
       : Type (a ⊔ ℓ)
     where
     constructor Lift
     field
       lower : A

   open ↑ public
