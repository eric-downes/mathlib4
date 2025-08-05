/-
Copyright (c) 2024 Mathlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: [Contributors]
-/
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.CategoryTheory.Limits.Types.Shapes
import Mathlib.CategoryTheory.Category.Preorder

/-!
# Tests for Products and Coproducts

This file tests products and coproducts in various categories.

## Coverage

- Binary products and coproducts
- General products indexed by a type
- HasBinaryProducts/HasBinaryCoproducts
- Product cones and their properties
- Concrete examples in Type*
-/

namespace CategoryTheoryTest.Products

open CategoryTheory CategoryTheory.Limits

noncomputable section

section BinaryProducts

variable {C : Type*} [Category C]

/-- Test WalkingPair -/
example : WalkingPair.left ≠ WalkingPair.right := by simp

/-- Test pair functor -/
example (X Y : C) : (pair X Y).obj ⟨WalkingPair.left⟩ = X := rfl
example (X Y : C) : (pair X Y).obj ⟨WalkingPair.right⟩ = Y := rfl

/-- Test binary product cone -/
example {X Y : C} [HasBinaryProduct X Y] : ∃ (c : BinaryFan X Y), IsLimit c :=
  ⟨BinaryFan.mk prod.fst prod.snd, prodIsProd⟩

/-- Test projections -/
example {X Y : C} [HasBinaryProduct X Y] : X ⨯ Y ⟶ X := prod.fst
example {X Y : C} [HasBinaryProduct X Y] : X ⨯ Y ⟶ Y := prod.snd

/-- Test universal property -/
example {X Y Z : C} [HasBinaryProduct X Y] (f : Z ⟶ X) (g : Z ⟶ Y) :
    ∃! h : Z ⟶ X ⨯ Y, h ≫ prod.fst = f ∧ h ≫ prod.snd = g := by
  use prod.lift f g
  constructor
  · simp
  · intro h' ⟨h1, h2⟩
    ext
    · simp [h1]
    · simp [h2]

/-- Product lift satisfies equations -/
example {X Y Z : C} [HasBinaryProduct X Y] (f : Z ⟶ X) (g : Z ⟶ Y) :
    prod.lift f g ≫ prod.fst = f := by simp

example {X Y Z : C} [HasBinaryProduct X Y] (f : Z ⟶ X) (g : Z ⟶ Y) :
    prod.lift f g ≫ prod.snd = g := by simp

/-- Uniqueness of product morphism -/
example {W X Y : C} [HasBinaryProduct X Y] (f g : W ⟶ X ⨯ Y) 
    (h1 : f ≫ prod.fst = g ≫ prod.fst) (h2 : f ≫ prod.snd = g ≫ prod.snd) : 
    f = g := by
  ext
  · exact h1
  · exact h2

end BinaryProducts

section BinaryCoproducts

variable {C : Type*} [Category C]

/-- Test binary coproduct cocone -/
example {X Y : C} [HasBinaryCoproduct X Y] : ∃ (c : BinaryCofan X Y), IsColimit c :=
  ⟨BinaryCofan.mk coprod.inl coprod.inr, coprodIsCoprod⟩

/-- Test injections -/
example {X Y : C} [HasBinaryCoproduct X Y] : X ⟶ X ⨿ Y := coprod.inl
example {X Y : C} [HasBinaryCoproduct X Y] : Y ⟶ X ⨿ Y := coprod.inr

/-- Test universal property -/
example {X Y Z : C} [HasBinaryCoproduct X Y] (f : X ⟶ Z) (g : Y ⟶ Z) :
    ∃! h : X ⨿ Y ⟶ Z, coprod.inl ≫ h = f ∧ coprod.inr ≫ h = g := by
  use coprod.desc f g
  constructor
  · simp
  · intro h' ⟨h1, h2⟩
    ext
    · simp [← h1]
    · simp [← h2]

end BinaryCoproducts

section TypeExamples

/-- Binary product in Type* is the product type -/
example (X Y : Type u) : (prod X Y : Type u) ≅ (Prod X Y) := Types.binaryProductIso _ _

/-- Test projections in Type* -/
example (X Y : Type*) : prod.fst = (Prod.fst : X × Y → X) := by
  -- Need to compare after the isomorphism
  ext ⟨x, y⟩
  rfl

/-- Binary coproduct in Type* is the sum type -/
example (X Y : Type*) : (X ⨿ Y : Type*) ≅ (X ⊕ Y) := Types.binaryCoproductIso _ _

/-- Concrete example with Nat and Bool -/
example : prod.lift (fun n : ℕ => n + 1) (fun n : ℕ => n % 2 = 0) = 
          fun n => (n + 1, n % 2 = 0) := by
  ext n
  constructor <;> rfl

end TypeExamples

section GeneralProducts

variable {C : Type*} [Category C]

/-- Fan for a family of objects -/
example {β : Type*} (f : β → C) (P : C) (π : ∀ b, P ⟶ f b) : Fan f :=
  Fan.mk P π

/-- Cofan for a family of objects -/
example {β : Type*} (f : β → C) (P : C) (ι : ∀ b, f b ⟶ P) : Cofan f :=
  Cofan.mk P ι

/-- Product of a family exists -/
example {β : Type*} (f : β → C) [HasProduct f] : Fan f :=
  productFan f

/-- Product projections -/
example {β : Type*} (f : β → C) [HasProduct f] (b : β) : (∏ᶜ f) ⟶ f b :=
  Pi.π f b

/-- Product lift -/
example {β : Type*} (f : β → C) [HasProduct f] {W : C} (g : ∀ b, W ⟶ f b) :
    W ⟶ ∏ᶜ f := Pi.lift g

/-- Lift composed with projection -/
example {β : Type*} (f : β → C) [HasProduct f] {W : C} (g : ∀ b, W ⟶ f b) (b : β) :
    Pi.lift g ≫ Pi.π f b = g b := by simp

end GeneralProducts

section Typeclasses

/-- Type* has all binary products -/
example : HasBinaryProducts (Type*) := inferInstance

/-- Type* has all binary coproducts -/
example : HasBinaryCoproducts (Type*) := inferInstance

/-- Type* has all products -/
example : HasProducts (Type*) := inferInstance

/-- Type* has all coproducts -/
example : HasCoproducts (Type*) := inferInstance

/-- A category with all binary products and terminal has all finite products -/
example {C : Type*} [Category C] [HasBinaryProducts C] [HasTerminal C] : 
    HasFiniteProducts C := ⟨inferInstance⟩

end Typeclasses

section PreorderProducts

/-- In a preorder with meets, binary product is the meet -/
example {P : Type*} [Preorder P] [HasInf P] (x y : P) : 
    @prod P _ x y = x ⊓ y := rfl

/-- In a preorder with joins, binary coproduct is the join -/
example {P : Type*} [Preorder P] [HasSup P] (x y : P) : 
    @coprod P _ x y = x ⊔ y := rfl

end PreorderProducts

section ProductComparison

variable {C D : Type*} [Category C] [Category D] (F : C ⥤ D)

/-- Product comparison morphism -/
example {X Y : C} [HasBinaryProduct X Y] [HasBinaryProduct (F.obj X) (F.obj Y)] :
    F.obj (X ⨯ Y) ⟶ F.obj X ⨯ F.obj Y :=
  prodComparison F X Y

/-- When F preserves binary products, the comparison is an iso -/
example {X Y : C} [HasBinaryProduct X Y] [HasBinaryProduct (F.obj X) (F.obj Y)]
    [PreservesBinaryProduct X Y F] :
    IsIso (prodComparison F X Y) := by
  apply PreservesBinaryProduct.iso

end ProductComparison

end -- noncomputable

end CategoryTheoryTest.Products

/-!
## Summary

This file tests:
1. Binary products and coproducts (~10 definitions)
2. General products and coproducts (~6 definitions)
3. Concrete examples in Type* (~4 definitions)
4. Typeclass instances (~4 definitions)
5. Product comparison morphisms (~2 definitions)

Total: ~26 key definitions tested
-/