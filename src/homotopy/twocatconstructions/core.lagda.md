---
title: "2-categorical constructions"
description: "Core: Whiskering and Horizontal Composition"
---

### Contents {#top}

1. [Whiskering](#whiskering)
1. [Horizontal composition](#horcomp)

--------------------------------------------------

```agda
{-# OPTIONS --without-K --safe #-}

module homotopy.twocatconstructions.core where

open import level
open import mltt.identity

open ≡-Reasoning
open ◾-lemmas
open ap-lemmas
```

### Whiskering {#whiskering}

Right and left whiskering. Whiskering is the composition, in the
horizontal direction of a 2-cell, i.e. identity of identity, with a
1-cell. This composition can be placed to the left or right of the
2-cell.

```agda
module _ {ℓ : Level} {A : Set ℓ} {x y z : A} where

  _◾ʳ_ : {p q : x ≡ y} (α : p ≡ q) (r : y ≡ z) → 
          p ◾ r ≡ q ◾ r
  α ◾ʳ r = ap (_◾ r) α

  _◾ˡ_ : (q : x ≡ y) {r s : y ≡ z} (β : r ≡ s) → 
          q ◾ r ≡ q ◾ s
  q ◾ˡ β = ap (q ◾_) β
```

The following two lemmas show that whiskering (on either side) by
reflexivity amounts to a conjugation.

```agda
module _ {ℓ : Level} {A : Set ℓ} {x y : A} where

  ◾ʳrefl : {p q : x ≡ y} (α : p ≡ q) → 
            α ◾ʳ (idp y) ≡ (ru p ◾ α) ◾ (ru q) ⁻¹
  ◾ʳrefl {p} {.(p)} refl = lemma ⁻¹
    where
      lemma = (ru p ◾ refl) ◾ ru p ⁻¹ ≡⟨ ap (_◾ ru p ⁻¹) (ru (ru p)) ⟩
              ru p ◾ ru p ⁻¹ ≡⟨ rinv (ru p) ⟩
              refl ∎

  refl◾ˡ : {r s : x ≡ y} (β : r ≡ s) → 
            (idp x) ◾ˡ β ≡ (lu r ◾ β) ◾ (lu s) ⁻¹
  refl◾ˡ {r} {.r} refl = refl
```

The next group of lemmas, the first two undo the whiskering, whereas
the last pair expresses the relation between whiskering and vertical
composition:

```agda
module _ {ℓ : Level} {A : Set ℓ} {x y z : A} where

  unwhisker-r : {p q : x ≡ y} (r : y ≡ z) →
            p ◾ r ≡ q ◾ r → p ≡ q
  unwhisker-r {p} {q} r α = p               ≡⟨  (ru p) ⁻¹ ⟩
                            p ◾ refl        ≡⟨ (p ◾ˡ (rinv r)) ⁻¹ ⟩
                            p ◾ (r ◾ r ⁻¹)  ≡⟨  (assoc p r (r ⁻¹)) ⁻¹  ⟩
                            (p ◾ r) ◾ r ⁻¹  ≡⟨ α ◾ʳ r ⁻¹  ⟩
                            (q ◾ r) ◾ r ⁻¹  ≡⟨ assoc q r (r ⁻¹)  ⟩
                            q ◾ (r ◾ r ⁻¹)  ≡⟨ q ◾ˡ (rinv r) ⟩
                            q ◾ refl        ≡⟨  ru q ⟩
                            q ∎

  syntax unwhisker-r r α =  α ◾⁻ʳ r


  unwhisker-l : (p : x ≡ y) {r s : y ≡ z} → 
                  p ◾ r ≡ p ◾ s → r ≡ s
  unwhisker-l p {r} {s} β = r              ≡⟨ refl ⟩
                            refl ◾ r       ≡⟨ (linv p) ⁻¹ ◾ʳ r ⟩
                            (p ⁻¹ ◾ p) ◾ r ≡⟨ assoc (p ⁻¹) p r ⟩
                            p ⁻¹ ◾ (p ◾ r) ≡⟨ p ⁻¹ ◾ˡ β ⟩
                            p ⁻¹ ◾ (p ◾ s) ≡⟨ (assoc (p ⁻¹) p s) ⁻¹ ⟩
                            (p ⁻¹ ◾ p) ◾ s ≡⟨ (linv p)  ◾ʳ s ⟩
                            s ∎

  syntax unwhisker-l p β = p ◾⁻ˡ β


  -- right whiskering and vertical composition
  _◾ᵥ_◾ʳ_ : {p q r : x ≡ y} 
             (α : p ≡ q) (β : q ≡ r) (u : y ≡ z) → 
             (α ◾ β) ◾ʳ u ≡ (α ◾ʳ u) ◾ (β ◾ʳ u)
  α ◾ᵥ β ◾ʳ u = ap◾ (_◾ u) α β


  -- left whiskering and vertical composition
  _◾ˡ_◾ᵥ_ : {u v w : y ≡ z}
             (p : x ≡ y) (γ : u ≡ v) (δ : v ≡ w) →
             p ◾ˡ (γ ◾ δ) ≡ (p ◾ˡ γ) ◾ (p ◾ˡ δ)
  p ◾ˡ γ ◾ᵥ δ = ap◾ (p ◾_) γ δ
```

<p style="font-size: smaller; text-align: right">[top ⇑](#top)</p>
---

### Horizontal composition {#horcomp}

Horizontal composition of 2-cells. There are two ways to do it, and we
prove they are equal:

```agda
module _ {ℓ : Level} {A : Set ℓ} {x y z : A} where
    
    _★_ : {p q : x ≡ y} {r s : y ≡ z}
           (α : p ≡ q) (β : r ≡ s) → p ◾ r ≡ q ◾ s
    _★_  {p} {q} {r} α β = (α ◾ʳ r) ◾ (q ◾ˡ β)

    _★′_ : {p q : x ≡ y} {r s : y ≡ z}
            (α : p ≡ q) (β : r ≡ s) → p ◾ r ≡ q ◾ s
    _★′_ {p} {q} {r} {s} α β = (p ◾ˡ β) ◾ (α ◾ʳ s)

    ★-is-★′ :  {p q : x ≡ y} {r s : y ≡ z}
                (α : p ≡ q) (β : r ≡ s) → α ★ β ≡ α ★′ β
    ★-is-★′ {p} refl β = (ru (ap (_◾_ p) β)) ⁻¹ 
```

We also need some obvious lemmas for the horizontal compositions `★` and `★′`

```agda
module ★-lemmas {ℓ : Level} {A : Set ℓ} {x y z : A} where

  lu★ : {p : x ≡ y} {r s : y ≡ z} (β : r ≡ s) →
        (idp p) ★ β ≡ p ◾ˡ β
  lu★ β = refl

  ru★ : {p q : x ≡ y} (α : p ≡ q) {r : y ≡ z} →
         α ★ (idp r) ≡ α ◾ʳ r
  ru★ α = ru _
```

<p style="font-size: smaller; text-align: right">[top ⇑](#top)</p>
---

