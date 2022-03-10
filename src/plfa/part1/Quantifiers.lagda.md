---
title     : "Quantifiers: Universals and existentials"
layout    : page
prev      : /Negation/
permalink : /Quantifiers/
next      : /Decidable/
---

```
module plfa.part1.Quantifiers where
```

This chapter introduces universal and existential quantification.

## Imports

```
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Relation.Nullary using (¬_)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import plfa.part1.Isomorphism using (_≃_; extensionality)
```


## Universals

We formalise universal quantification using the dependent function
type, which has appeared throughout this book.  For instance, in
Chapter Induction we showed addition is associative:

    +-assoc : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)

which asserts for all natural numbers `m`, `n`, and `p`
that `(m + n) + p ≡ m + (n + p)` holds.  It is a dependent
function, which given values for `m`, `n`, and `p` returns
evidence for the corresponding equation.

In general, given a variable `x` of type `A` and a proposition `B x`
which contains `x` as a free variable, the universally quantified
proposition `∀ (x : A) → B x` holds if for every term `M` of type `A`
the proposition `B M` holds.  Here `B M` stands for the proposition
`B x` with each free occurrence of `x` replaced by `M`.  Variable `x`
appears free in `B x` but bound in `∀ (x : A) → B x`.

Evidence that `∀ (x : A) → B x` holds is of the form

    λ (x : A) → N x

where `N x` is a term of type `B x`, and `N x` and `B x` both contain
a free variable `x` of type `A`.  Given a term `L` providing evidence
that `∀ (x : A) → B x` holds, and a term `M` of type `A`, the term `L M`
provides evidence that `B M` holds.  In other words, evidence that
`∀ (x : A) → B x` holds is a function that converts a term `M` of type
`A` into evidence that `B M` holds.

Put another way, if we know that `∀ (x : A) → B x` holds and that `M`
is a term of type `A` then we may conclude that `B M` holds:
```
∀-elim : ∀ {A : Set} {B : A → Set}
  → (L : ∀ (x : A) → B x)
  → (M : A)
    -----------------
  → B M
∀-elim L M = L M
```
As with `→-elim`, the rule corresponds to function application.

Functions arise as a special case of dependent functions,
where the range does not depend on a variable drawn from the domain.
When a function is viewed as evidence of implication, both its
argument and result are viewed as evidence, whereas when a dependent
function is viewed as evidence of a universal, its argument is viewed
as an element of a data type and its result is viewed as evidence of
a proposition that depends on the argument. This difference is largely
a matter of interpretation, since in Agda a value of a type and
evidence of a proposition are indistinguishable.

Dependent function types are sometimes referred to as dependent
products, because if `A` is a finite type with values `x₁ , ⋯ , xₙ`,
and if each of the types `B x₁ , ⋯ , B xₙ` has `m₁ , ⋯ , mₙ` distinct
members, then `∀ (x : A) → B x` has `m₁ * ⋯ * mₙ` members.  Indeed,
sometimes the notation `∀ (x : A) → B x` is replaced by a notation
such as `Π[ x ∈ A ] (B x)`, where `Π` stands for product.  However, we
will stick with the name dependent function, because (as we will see)
dependent product is ambiguous.


#### Exercise `∀-distrib-×` (recommended)

Show that universals distribute over conjunction:
```
∀-distrib-× : ∀ {A : Set} {B C : A → Set} →
  (∀ (x : A) → B x × C x) ≃ (∀ (x : A) → B x) × (∀ (x : A) → C x)

∀-distrib-× = record {
   to = λ f → ⟨ (λ a → proj₁ (f a)) , (λ x → proj₂ (f x)) ⟩ ;
   from = λ{ ⟨ fst , snd ⟩ a → ⟨ fst a , snd a ⟩ };
   from∘to = λ x → refl ;
   to∘from = λ y → refl
   }
```
Compare this with the result (`→-distrib-×`) in
Chapter [Connectives](/Connectives/).

#### Exercise `⊎∀-implies-∀⊎` (practice)

Show that a disjunction of universals implies a universal of disjunctions:
```
⊎∀-implies-∀⊎ : ∀ {A : Set} {B C : A → Set} →
  (∀ (x : A) → B x) ⊎ (∀ (x : A) → C x) → ∀ (x : A) → B x ⊎ C x

⊎∀-implies-∀⊎ (inj₁ f) a = inj₁ (f a)
⊎∀-implies-∀⊎ (inj₂ f) a = inj₂ (f a)
```
Does the converse hold? If so, prove; if not, explain why.
```
-- the converse doesn't hold because...
-- the left side gives the user the ability to decide which of B or C they want,
-- whereas the right lets the implementer make that decision.
-- if the user decides they want B, but the right side gives us C, we're doomed.
```


#### Exercise `∀-×` (practice)

Consider the following type.
```
data Tri : Set where
  aa : Tri
  bb : Tri
  cc : Tri
```
Let `B` be a type indexed by `Tri`, that is `B : Tri → Set`.
Show that `∀ (x : Tri) → B x` is isomorphic to `B aa × B bb × B cc`.
Hint: you will need to postulate a version of extensionality that
works for dependent functions.

```
postulate
  ∀-extensionality : ∀ {A : Set} {B : A → Set} {f g : ∀ (x : A) → B x}
    → (∀ (x : A) → f x ≡ g x)
      -----------------------
    → f ≡ g

∀-× : ∀ (B : Tri → Set) → (∀ (x : Tri) → B x) ≃ B aa × B bb × B cc
_≃_.to (∀-× B) f = ⟨ (f aa) , ⟨ (f bb) , (f cc) ⟩ ⟩
_≃_.from (∀-× B) ⟨ Baa , ⟨ Bbb , Bcc ⟩ ⟩ aa = Baa
_≃_.from (∀-× B) ⟨ Baa , ⟨ Bbb , Bcc ⟩ ⟩ bb = Bbb
_≃_.from (∀-× B) ⟨ Baa , ⟨ Bbb , Bcc ⟩ ⟩ cc = Bcc
_≃_.from∘to (∀-× B) f = ∀-extensionality λ{ aa → refl ; bb → refl ; cc → refl }
_≃_.to∘from (∀-× B) ⟨ Baa , ⟨ Bbb , Bcc ⟩ ⟩ = refl
```

## Existentials

Given a variable `x` of type `A` and a proposition `B x` which
contains `x` as a free variable, the existentially quantified
proposition `Σ[ x ∈ A ] B x` holds if for some term `M` of type
`A` the proposition `B M` holds.  Here `B M` stands for
the proposition `B x` with each free occurrence of `x` replaced by
`M`.  Variable `x` appears free in `B x` but bound in
`Σ[ x ∈ A ] B x`.

We formalise existential quantification by declaring a suitable
inductive type:
```
data Σ (A : Set) (B : A → Set) : Set where
  ⟨_,_⟩ : (x : A) → B x → Σ A B
```
We define a convenient syntax for existentials as follows:
```
Σ-syntax = Σ
infix 2 Σ-syntax
syntax Σ-syntax A (λ x → B) = Σ[ x ∈ A ] B
```
This is our first use of a syntax declaration, which specifies that
the term on the left may be written with the syntax on the right.
The special syntax is available only when the identifier
`Σ-syntax` is imported.

Evidence that `Σ[ x ∈ A ] B x` holds is of the form
`⟨ M , N ⟩` where `M` is a term of type `A`, and `N` is evidence
that `B M` holds.

Equivalently, we could also declare existentials as a record type:
```
record Σ′ (A : Set) (B : A → Set) : Set where
  field
    proj₁′ : A
    proj₂′ : B proj₁′
```
Here record construction

    record
      { proj₁′ = M
      ; proj₂′ = N
      }

corresponds to the term

    ⟨ M , N ⟩

where `M` is a term of type `A` and `N` is a term of type `B M`.

Products arise as a special case of existentials, where the second
component does not depend on a variable drawn from the first
component.  When a product is viewed as evidence of a conjunction,
both of its components are viewed as evidence, whereas when it is
viewed as evidence of an existential, the first component is viewed as
an element of a datatype and the second component is viewed as
evidence of a proposition that depends on the first component.  This
difference is largely a matter of interpretation, since in Agda a value
of a type and evidence of a proposition are indistinguishable.

Existentials are sometimes referred to as dependent sums,
because if `A` is a finite type with values `x₁ , ⋯ , xₙ`, and if
each of the types `B x₁ , ⋯ B xₙ` has `m₁ , ⋯ , mₙ` distinct members,
then `Σ[ x ∈ A ] B x` has `m₁ + ⋯ + mₙ` members, which explains the
choice of notation for existentials, since `Σ` stands for sum.

Existentials are sometimes referred to as dependent products, since
products arise as a special case.  However, that choice of names is
doubly confusing, since universals also have a claim to the name dependent
product and since existentials also have a claim to the name dependent sum.

A common notation for existentials is `∃` (analogous to `∀` for universals).
We follow the convention of the Agda standard library, and reserve this
notation for the case where the domain of the bound variable is left implicit:
```
∃ : ∀ {A : Set} (B : A → Set) → Set
∃ {A} B = Σ A B

∃-syntax = ∃
syntax ∃-syntax (λ x → B) = ∃[ x ] B
```
The special syntax is available only when the identifier `∃-syntax` is imported.
We will tend to use this syntax, since it is shorter and more familiar.

Given evidence that `∀ x → B x → C` holds, where `C` does not contain
`x` as a free variable, and given evidence that `∃[ x ] B x` holds, we
may conclude that `C` holds:
```
∃-elim : ∀ {A : Set} {B : A → Set} {C : Set}
  → (∀ x → B x → C)
  → ∃[ x ] B x
    ---------------
  → C
∃-elim f ⟨ x , y ⟩ = f x y
```
In other words, if we know for every `x` of type `A` that `B x`
implies `C`, and we know for some `x` of type `A` that `B x` holds,
then we may conclude that `C` holds.  This is because we may
instantiate that proof that `∀ x → B x → C` to any value `x` of type
`A` and any `y` of type `B x`, and exactly such values are provided by
the evidence for `∃[ x ] B x`.

Indeed, the converse also holds, and the two together form an isomorphism:
```
∀∃-currying : ∀ {A : Set} {B : A → Set} {C : Set}
  → (∀ x → B x → C) ≃ (∃[ x ] B x → C)
∀∃-currying =
  record
    { to      =  λ{ f → λ{ ⟨ x , y ⟩ → f x y }}
    ; from    =  λ{ g → λ{ x → λ{ y → g ⟨ x , y ⟩ }}}
    ; from∘to =  λ{ f → refl }
    ; to∘from =  λ{ g → extensionality λ{ ⟨ x , y ⟩ → refl }}
    }
```
The result can be viewed as a generalisation of currying.  Indeed, the code to
establish the isomorphism is identical to what we wrote when discussing
[implication](/Connectives/#implication).

#### Exercise `∃-distrib-⊎` (recommended)

Show that existentials distribute over disjunction:
```
∃-distrib-⊎ : ∀ {A : Set} {B C : A → Set} →
  ∃[ x ] (B x ⊎ C x) ≃ (∃[ x ] B x) ⊎ (∃[ x ] C x)
∃-distrib-⊎ =
  record
    { to = λ{ ⟨ a , inj₁ x ⟩ → inj₁ ⟨ a , x ⟩ ; ⟨ a , inj₂ y ⟩ → inj₂ ⟨ a , y ⟩}
    ; from = λ{ (inj₁ ⟨ x , Bx ⟩) → ⟨ x , inj₁ Bx ⟩ ; (inj₂ ⟨ x , Cx ⟩) → ⟨ x , (inj₂ Cx) ⟩}
    ; from∘to = λ{ ⟨ a , inj₁ ba ⟩ → refl ; ⟨ a , inj₂ ca ⟩ → refl}
    ; to∘from = λ{ (inj₁ ⟨ x , x₁ ⟩) → refl ; (inj₂ ⟨ x , x₁ ⟩) → refl}
    }
```

#### Exercise `∃×-implies-×∃` (practice)

Show that an existential of conjunctions implies a conjunction of existentials:
```
∃×-implies-×∃ : ∀ {A : Set} {B C : A → Set} →
  ∃[ x ] (B x × C x) → (∃[ x ] B x) × (∃[ x ] C x)
∃×-implies-×∃ ⟨ a , ⟨ Ba , Ca ⟩ ⟩ = ⟨ ⟨ a , Ba ⟩ , ⟨ a , Ca ⟩ ⟩
```
Does the converse hold? If so, prove; if not, explain why.

```
-- no because we can't necessarily find a single x for which both B and C are true,
-- just given a ∃[ x ] B x and ∃[ x ] C x.
-- we'd need intersection types or something
```

#### Exercise `∃-⊎` (practice)

Let `Tri` and `B` be as in Exercise `∀-×`.
Show that `∃[ x ] B x` is isomorphic to `B aa ⊎ B bb ⊎ B cc`.

```
∃-⊎ : ∀ (B : Tri → Set) → ∃[ x ] B x ≃ B aa ⊎ B bb ⊎ B cc
∃-⊎ B =
  record
  { to = λ{ ⟨ aa , Bx ⟩ → inj₁ Bx
          ; ⟨ bb , Bx ⟩ → inj₂ (inj₁ Bx)
          ; ⟨ cc , Bx ⟩ → inj₂ (inj₂ Bx)}
  ; from = λ{ (inj₁ Baa) → ⟨ aa , Baa ⟩
            ; (inj₂ (inj₁ Bbb)) → ⟨ bb , Bbb ⟩
            ; (inj₂ (inj₂ Bcc)) → ⟨ cc , Bcc ⟩}
  ; from∘to = λ{ ⟨ aa , x₁ ⟩ → refl ; ⟨ bb , x₁ ⟩ → refl ; ⟨ cc , x₁ ⟩ → refl}
  ; to∘from = λ{ (inj₁ x) → refl ; (inj₂ (inj₁ x)) → refl ; (inj₂ (inj₂ y)) → refl}
  }
```

## An existential example

Recall the definitions of `even` and `odd` from
Chapter [Relations](/Relations/):
```
data even : ℕ → Set
data odd  : ℕ → Set

data even where

  even-zero : even zero

  even-suc : ∀ {n : ℕ}
    → odd n
      ------------
    → even (suc n)

data odd where
  odd-suc : ∀ {n : ℕ}
    → even n
      -----------
    → odd (suc n)
```
A number is even if it is zero or the successor of an odd number, and
odd if it is the successor of an even number.

We will show that a number is even if and only if it is twice some
other number, and odd if and only if it is one more than twice
some other number.  In other words, we will show:

`even n`   iff   `∃[ m ] (    m * 2 ≡ n)`

`odd  n`   iff   `∃[ m ] (1 + m * 2 ≡ n)`

By convention, one tends to write constant factors first and to put
the constant term in a sum last. Here we've reversed each of those
conventions, because doing so eases the proof.

Here is the proof in the forward direction:
```
even-∃ : ∀ {n : ℕ} → even n → ∃[ m ] (    m * 2 ≡ n)
odd-∃  : ∀ {n : ℕ} →  odd n → ∃[ m ] (1 + m * 2 ≡ n)

even-∃ even-zero                       =  ⟨ zero , refl ⟩
even-∃ (even-suc o) with odd-∃ o
...                    | ⟨ m , refl ⟩  =  ⟨ suc m , refl ⟩

odd-∃  (odd-suc e)  with even-∃ e
...                    | ⟨ m , refl ⟩  =  ⟨ m , refl ⟩
```
We define two mutually recursive functions. Given
evidence that `n` is even or odd, we return a
number `m` and evidence that `m * 2 ≡ n` or `1 + m * 2 ≡ n`.
We induct over the evidence that `n` is even or odd:

* If the number is even because it is zero, then we return a pair
consisting of zero and the evidence that twice zero is zero.

* If the number is even because it is one more than an odd number,
then we apply the induction hypothesis to give a number `m` and
evidence that `1 + m * 2 ≡ n`. We return a pair consisting of `suc m`
and evidence that `suc m * 2 ≡ suc n`, which is immediate after
substituting for `n`.

* If the number is odd because it is the successor of an even number,
then we apply the induction hypothesis to give a number `m` and
evidence that `m * 2 ≡ n`. We return a pair consisting of `suc m` and
evidence that `1 + m * 2 ≡ suc n`, which is immediate after
substituting for `n`.

This completes the proof in the forward direction.

Here is the proof in the reverse direction:
```
∃-even : ∀ {n : ℕ} → ∃[ m ] (    m * 2 ≡ n) → even n
∃-odd  : ∀ {n : ℕ} → ∃[ m ] (1 + m * 2 ≡ n) →  odd n

∃-even ⟨  zero , refl ⟩  =  even-zero
∃-even ⟨ suc m , refl ⟩  =  even-suc (∃-odd ⟨ m , refl ⟩)

∃-odd  ⟨     m , refl ⟩  =  odd-suc (∃-even ⟨ m , refl ⟩)
```
Given a number that is twice some other number we must show it is
even, and a number that is one more than twice some other number we
must show it is odd.  We induct over the evidence of the existential,
and in the even case consider the two possibilities for the number
that is doubled:

- In the even case for `zero`, we must show `zero * 2` is even, which
follows by `even-zero`.

- In the even case for `suc n`, we must show `suc m * 2` is even.  The
inductive hypothesis tells us that `1 + m * 2` is odd, from which the
desired result follows by `even-suc`.

- In the odd case, we must show `1 + m * 2` is odd.  The inductive
hypothesis tell us that `m * 2` is even, from which the desired result
follows by `odd-suc`.

This completes the proof in the backward direction.

#### Exercise `∃-even-odd` (practice)

How do the proofs become more difficult if we replace `m * 2` and `1 + m * 2`
by `2 * m` and `2 * m + 1`?  Rewrite the proofs of `∃-even` and `∃-odd` when
restated in this way.

```
even-∃' : ∀ {n : ℕ} → even n → ∃[ m ] (2 * m     ≡ n)
odd-∃'  : ∀ {n : ℕ} →  odd n → ∃[ m ] (2 * m + 1 ≡ n)

open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open Eq using (cong; sym)
open import Data.Nat.Properties using (+-assoc; *-comm)
open import plfa.part1.Induction using (+-identityʳ; +-suc)

suc-+ʳ : ∀ {x : ℕ} → suc x ≡ x + 1
suc-+ʳ {zero} = refl
suc-+ʳ {suc x} = cong suc suc-+ʳ

even-∃' even-zero = ⟨ zero , refl ⟩
even-∃' (even-suc o) with odd-∃' o
... | ⟨ x , refl ⟩ = ⟨ suc x , begin
  suc (x + suc (x + 0))
  ≡⟨ cong suc (cong (x +_) suc-+ʳ) ⟩
  suc (x + ((x + 0) + 1))
  ≡⟨ cong suc (sym (+-assoc x (x + 0) 1)) ⟩
  suc (x + (x + 0) + 1)
  ∎ ⟩
odd-∃' (odd-suc e) with even-∃' e
... | ⟨ x , refl ⟩ = ⟨ x , sym suc-+ʳ ⟩

m*2≡+ : ∀ (m : ℕ) → m * 2 ≡ m + m
m*2≡+ zero = refl
m*2≡+ (suc m) = cong suc (begin
  suc (m * 2)
  ≡⟨ cong suc (m*2≡+ m) ⟩
  suc (m + m)
  ≡⟨ sym (+-suc m m) ⟩
  m + suc m
  ∎)

∃-even' : ∀ {n : ℕ} → ∃[ m ] (2 * m     ≡ n) → even n
∃-odd'  : ∀ {n : ℕ} → ∃[ m ] (2 * m + 1 ≡ n) →  odd n
∃-even' ⟨ zero , refl ⟩ = even-zero
∃-even' ⟨ suc m , refl ⟩ = even-suc (∃-odd' ⟨ m , begin
  (m + (m + 0)) + 1
  ≡⟨ +-assoc m (m + 0) 1 ⟩
  m + ((m + 0) + 1)
  ≡⟨ cong (m +_) (sym suc-+ʳ) ⟩
  m + suc (m + 0)
  ∎ ⟩)
∃-odd' ⟨ m , refl ⟩ rewrite +-identityʳ m | sym (suc-+ʳ {m + m}) = odd-suc (∃-even ⟨ m , m*2≡+ m ⟩)
-- they become harder because of insane bad normalization stuff something something
```

#### Exercise `∃-+-≤` (practice)

Show that `y ≤ z` holds if and only if there exists a `x` such that
`x + y ≡ z`.

```
open import Data.Nat using (_≤_; z≤n; s≤s)
open import plfa.part1.Isomorphism using (_⇔_)
open _⇔_

∃-+-≤ : ∀ (y z : ℕ) → y ≤ z ⇔ (∃[ x ] (x + y ≡ z))
-- ∃-+-≤ y z = {!!}
to (∃-+-≤ zero z) z≤n = ⟨ z , +-identityʳ z ⟩
to (∃-+-≤ (suc y) (suc z)) (s≤s y≤z) with to (∃-+-≤ y z) y≤z
... | ⟨ x , x+y≡z ⟩ = ⟨ x , begin
  x + suc y
  ≡⟨ +-suc x y ⟩
  suc (x + y)
  ≡⟨ cong suc x+y≡z ⟩
  suc z
  ∎ ⟩
from (∃-+-≤ zero z) ⟨ x , x+y≡z ⟩ = z≤n
from (∃-+-≤ (suc y) .(x + suc y)) ⟨ x , refl ⟩ rewrite +-suc x y = s≤s (from (∃-+-≤ y (x + y)) ⟨ x , refl ⟩)
```


## Existentials, Universals, and Negation

Negation of an existential is isomorphic to the universal
of a negation.  Considering that existentials are generalised
disjunction and universals are generalised conjunction, this
result is analogous to the one which tells us that negation
of a disjunction is isomorphic to a conjunction of negations:
```
¬∃≃∀¬ : ∀ {A : Set} {B : A → Set}
  → (¬ ∃[ x ] B x) ≃ ∀ x → ¬ B x
¬∃≃∀¬ =
  record
    { to      =  λ{ ¬∃xy x y → ¬∃xy ⟨ x , y ⟩ }
    ; from    =  λ{ ∀¬xy ⟨ x , y ⟩ → ∀¬xy x y }
    ; from∘to =  λ{ ¬∃xy → extensionality λ{ ⟨ x , y ⟩ → refl } }
    ; to∘from =  λ{ ∀¬xy → refl }
    }
```
In the `to` direction, we are given a value `¬∃xy` of type
`¬ ∃[ x ] B x`, and need to show that given a value
`x` that `¬ B x` follows, in other words, from
a value `y` of type `B x` we can derive false.  Combining
`x` and `y` gives us a value `⟨ x , y ⟩` of type `∃[ x ] B x`,
and applying `¬∃xy` to that yields a contradiction.

In the `from` direction, we are given a value `∀¬xy` of type
`∀ x → ¬ B x`, and need to show that from a value `⟨ x , y ⟩`
of type `∃[ x ] B x` we can derive false.  Applying `∀¬xy`
to `x` gives a value of type `¬ B x`, and applying that to `y` yields
a contradiction.

The two inverse proofs are straightforward, where one direction
requires extensionality.


#### Exercise `∃¬-implies-¬∀` (recommended)

Show that existential of a negation implies negation of a universal:
```
∃¬-implies-¬∀ : ∀ {A : Set} {B : A → Set}
    → ∃[ x ] (¬ B x)
      --------------
    → ¬ (∀ x → B x)

∃¬-implies-¬∀ ⟨ a , ¬Ba ⟩ a→Ba = ¬Ba (a→Ba a)
```
Does the converse hold? If so, prove; if not, explain why.
```
-- ¬∀-implies-∃¬ : ∀ {A : Set} {B : A → Set}
--     → ¬ (∀ x → B x)
--     → ∃[ x ] (¬ B x)

-- it seems like it *should* hold,
-- because a constructive proof of ¬ (∀ x → B x) should have a counterexample somehow.
-- but it doesn't seem to hold,
-- because we can't get a concrete x to serve as our counterexample
-- and we need a concrete x because this existential doesn't hide x...
-- but it seems like system F existentials which do hide x should be able to do it...
-- since you can't actually touch x then...
```


#### Exercise `Bin-isomorphism` (stretch) {#Bin-isomorphism}

Recall that Exercises
[Bin](/Naturals/#Bin),
[Bin-laws](/Induction/#Bin-laws), and
[Bin-predicates](/Relations/#Bin-predicates)
define a datatype `Bin` of bitstrings representing natural numbers,
and asks you to define the following functions and predicates:

    to   : ℕ → Bin
    from : Bin → ℕ
    Can  : Bin → Set

And to establish the following properties:

    from (to n) ≡ n

    ----------
    Can (to n)

    Can b
    ---------------
    to (from b) ≡ b

Using the above, establish that there is an isomorphism between `ℕ` and
`∃[ b ] Can b`.

We recommend proving the following lemmas which show that, for a given
binary number `b`, there is only one proof of `One b` and similarly
for `Can b`.

    ≡One : ∀ {b : Bin} (o o′ : One b) → o ≡ o′

    ≡Can : ∀ {b : Bin} (cb cb′ : Can b) → cb ≡ cb′

Many of the alternatives for proving `to∘from` turn out to be tricky.
However, the proof can be straightforward if you use the following lemma,
which is a corollary of `≡Can`.

    proj₁≡→Can≡ : {cb cb′ : ∃[ b ] Can b} → proj₁ cb ≡ proj₁ cb′ → cb ≡ cb′

```
open import plfa.part1.Relations using (Bin; ⟨⟩; _O; _I; inc; Can; One; to-can; can-roundtrip)
import plfa.part1.Relations as B using (from; to)
open import plfa.part1.Isomorphism using (ℕ-roundtrip)

≡One : ∀ {b : Bin} (o o′ : One b) → o ≡ o′
≡One One.⟨I⟩ One.⟨I⟩ = refl
≡One (o O) (o' O) = cong _O (≡One o o')
≡One (o I) (o' I) = cong _I (≡One o o')

≡Can : ∀ {b : Bin} (cb cb′ : Can b) → cb ≡ cb′
≡Can Can.zero Can.zero = refl
≡Can (Can.lead x) (Can.lead x') = cong Can.lead (≡One x x')
≡Can (Can.lead (() O)) Can.zero
≡Can Can.zero (Can.lead (() O))

proj1 : ∀ {A : Set} {P : A → Set} → Σ[ x ∈ A ] P x → A
proj1 ⟨ a , _ ⟩ = a

proj₁≡→Can≡ : ∀ {cb cb′ : Σ[ b ∈ Bin ] Can b} → (proj1 cb ≡ proj1 cb′) → cb ≡ cb′
proj₁≡→Can≡ {⟨ x , cb ⟩} {⟨ .x , cb' ⟩} refl = cong ⟨ x ,_⟩ (≡Can cb cb')

ℕ≃∃Can : ℕ ≃ (Σ[ b ∈ Bin ] Can b)
_≃_.to ℕ≃∃Can n = ⟨ B.to n , to-can n ⟩
_≃_.from ℕ≃∃Can ⟨ b , cb ⟩ = B.from b
_≃_.from∘to ℕ≃∃Can = ℕ-roundtrip
_≃_.to∘from ℕ≃∃Can ⟨ b , cb ⟩ = proj₁≡→Can≡ (can-roundtrip b cb)
```


## Standard library

Definitions similar to those in this chapter can be found in the standard library:
```
import Data.Product using (Σ; _,_; ∃; Σ-syntax; ∃-syntax)
```


## Unicode

This chapter uses the following unicode:

    Π  U+03A0  GREEK CAPITAL LETTER PI (\Pi)
    Σ  U+03A3  GREEK CAPITAL LETTER SIGMA (\Sigma)
    ∃  U+2203  THERE EXISTS (\ex, \exists)
