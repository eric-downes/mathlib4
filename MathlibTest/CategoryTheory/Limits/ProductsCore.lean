/-
Copyright (c) 2024 Mathlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: [Contributors]
-/
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Limits.Types.Shapes

/-!
# Core Tests for Products and Coproducts

This file tests essential APIs for products and coproducts.

## Coverage

- Binary products/coproducts
- Product/coproduct morphisms
- Universal properties
- Basic examples in Type*
-/

namespace CategoryTheoryTest.ProductsCore

open CategoryTheory CategoryTheory.Limits

noncomputable section

section BinaryProducts

variable {C : Type*} [Category C]

/-- WalkingPair as index -/
example : WalkingPair.left ≠ WalkingPair.right := by simp

/-- Binary product exists -/
example {X Y : C} [HasBinaryProduct X Y] : C := X ⨯ Y

/-- Product projections -/
example {X Y : C} [HasBinaryProduct X Y] : X ⨯ Y ⟶ X := prod.fst
example {X Y : C} [HasBinaryProduct X Y] : X ⨯ Y ⟶ Y := prod.snd

/-- Product lift -/
example {X Y Z : C} [HasBinaryProduct X Y] (f : Z ⟶ X) (g : Z ⟶ Y) :
    Z ⟶ X ⨯ Y := prod.lift f g

/-- Lift equations -/
example {X Y Z : C} [HasBinaryProduct X Y] (f : Z ⟶ X) (g : Z ⟶ Y) :
    prod.lift f g ≫ prod.fst = f := by simp

example {X Y Z : C} [HasBinaryProduct X Y] (f : Z ⟶ X) (g : Z ⟶ Y) :
    prod.lift f g ≫ prod.snd = g := by simp

/-- Universal property -/
example {W X Y : C} [HasBinaryProduct X Y] (h : W ⟶ X ⨯ Y) :
    h = prod.lift (h ≫ prod.fst) (h ≫ prod.snd) := by
  ext <;> simp

end BinaryProducts

section BinaryCoproducts

variable {C : Type*} [Category C]

/-- Binary coproduct exists -/
example {X Y : C} [HasBinaryCoproduct X Y] : C := X ⨿ Y

/-- Coproduct injections -/
example {X Y : C} [HasBinaryCoproduct X Y] : X ⟶ X ⨿ Y := coprod.inl
example {X Y : C} [HasBinaryCoproduct X Y] : Y ⟶ X ⨿ Y := coprod.inr

/-- Coproduct desc -/
example {X Y Z : C} [HasBinaryCoproduct X Y] (f : X ⟶ Z) (g : Y ⟶ Z) :
    X ⨿ Y ⟶ Z := coprod.desc f g

/-- Desc equations -/
example {X Y Z : C} [HasBinaryCoproduct X Y] (f : X ⟶ Z) (g : Y ⟶ Z) :
    coprod.inl ≫ coprod.desc f g = f := by simp

example {X Y Z : C} [HasBinaryCoproduct X Y] (f : X ⟶ Z) (g : Y ⟶ Z) :
    coprod.inr ≫ coprod.desc f g = g := by simp

end BinaryCoproducts

section TypeExamples

/-- Type has binary products -/
instance : HasBinaryProducts.{u} (Type u) := inferInstance

/-- Type has binary coproducts -/
instance : HasBinaryCoproducts.{u} (Type u) := inferInstance

/-- Binary product in Type is product type -/
example (X Y : Type u) : Nonempty ((prod X Y : Type u) ≅ (Prod X Y)) :=
  ⟨Types.binaryProductIso _ _⟩

/-- Binary coproduct in Type is sum type -/
example (X Y : Type u) : Nonempty ((coprod X Y : Type u) ≅ (Sum X Y)) :=
  ⟨Types.binaryCoproductIso _ _⟩


end TypeExamples

section GeneralProducts

variable {C : Type*} [Category C]

/-- Product indexed by type -/
example {β : Type*} (f : β → C) [HasProduct f] : C := ∏ᶜ f

/-- Product projections -/
example {β : Type*} (f : β → C) [HasProduct f] (b : β) : (∏ᶜ f) ⟶ f b :=
  Pi.π f b

/-- Product lift -/
example {β : Type*} (f : β → C) [HasProduct f] {W : C} (g : ∀ b, W ⟶ f b) :
    W ⟶ ∏ᶜ f := Pi.lift g

/-- Lift equation -/
example {β : Type*} (f : β → C) [HasProduct f] {W : C} (g : ∀ b, W ⟶ f b) (b : β) :
    Pi.lift g ≫ Pi.π f b = g b := by simp

end GeneralProducts

section Typeclasses

/-- HasBinaryProducts instance -/
example : HasBinaryProducts (Type u) := inferInstance

/-- HasProducts instance -/
example : HasProducts.{u} (Type u) := inferInstance


end Typeclasses

end -- noncomputable

end CategoryTheoryTest.ProductsCore

/-!
## Summary

Core functionality tested:
- Binary products/coproducts (~8 definitions)
- Universal properties (~4 definitions)
- Type examples (~4 definitions)
- General products (~4 definitions)
- Typeclass instances (~3 definitions)

Total: ~20 key definitions tested
-/