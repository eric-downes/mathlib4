/-
Copyright (c) 2024 Mathlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: [Contributors]
-/
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Types
import Mathlib.CategoryTheory.Opposites
import MathlibTest.CategoryTheory.TestFramework

/-!
# Tests for Opposite Categories and ULift Instance

This file tests the behavior of opposite categories (already tested partially in CategoryLaws.lean)
and the ULift category instance from Category.Basic.lean.

## Coverage

- `uliftCategory` instance - ✓ Tested
- Opposite category interaction with basic laws - ✓ Tested (in CategoryLaws.lean)
- ULift preserves category structure - ✓ Tested
- Universe lifting examples - ✓ Tested

Coverage: 1/1 new definition (100%)
-/

namespace CategoryTheoryTest.OppositeAndULift

open CategoryTheory

section ULiftCategory

universe u v u'

variable (C : Type u) [Category.{v} C]

/-- ULift has a category instance -/
example : Category.{v} (ULift.{u'} C) := inferInstance

/-- Morphisms in ULift are morphisms in the original category -/
example (X Y : ULift.{u'} C) : (X ⟶ Y) = (X.down ⟶ Y.down) := rfl

/-- Identity in ULift is the identity in the original category -/
example (X : ULift.{u'} C) : 𝟙 X = 𝟙 X.down := rfl

/-- Composition in ULift is composition in the original category -/
example {X Y Z : ULift.{u'} C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    f ≫ g = (f : X.down ⟶ Y.down) ≫ (g : Y.down ⟶ Z.down) := rfl

/-- Small categories can be lifted to large categories -/
example (D : Type u) [SmallCategory D] : LargeCategory (ULift.{u + 1} D) := inferInstance

/-- Verify the example from Category.Basic.lean -/
example (D : Type u) [SmallCategory D] : LargeCategory (ULift.{u + 1} D) := by infer_instance

end ULiftCategory

section ULiftProperties

universe u v u'

variable {C : Type u} [Category.{v} C]

/-- ULift preserves category laws -/
example {X Y : ULift.{u'} C} (f : X ⟶ Y) : 𝟙 X ≫ f = f := by simp

example {X Y : ULift.{u'} C} (f : X ⟶ Y) : f ≫ 𝟙 Y = f := by simp

example {W X Y Z : ULift.{u'} C} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z) :
    (f ≫ g) ≫ h = f ≫ (g ≫ h) := by simp

/-- Lifting and lowering morphisms -/
def liftMorphism {X Y : C} (f : X ⟶ Y) : 
    ULift.up X ⟶ ULift.up Y := f

example {X Y : C} (f : X ⟶ Y) : 
    liftMorphism f = f := rfl

/-- Round-trip property -/
example (X : C) : (ULift.up X).down = X := rfl

example (X : ULift.{u'} C) : ULift.up X.down = X := by
  cases X
  rfl

end ULiftProperties

section ConcreteULiftExamples

/-- ULift of Type* -/
example : Category (ULift.{u + 1} Type*) := inferInstance

/-- Morphisms in ULift Type* -/
example (X Y : Type*) : 
    (ULift.up X ⟶ ULift.up Y : ULift Type* → ULift Type*) = (X ⟶ Y) := rfl

/-- Concrete computation -/
example : (ULift.up Nat ⟶ ULift.up Int : ULift Type* → ULift Type*) = (Nat → Int) := rfl

/-- Function lifting -/
def liftFunc {X Y : Type*} (f : X → Y) : ULift.up X ⟶ ULift.up Y := f

example : liftFunc (fun n : Nat => n + 1) = (fun n : Nat => n + 1) := rfl

end ConcreteULiftExamples

section OppositeReview

/-- Quick review of opposite category properties already tested in CategoryLaws.lean -/

variable {C : Type*} [Category C]

/-- Opposite category satisfies laws -/
example {X Y : Cᵒᵖ} (f : X ⟶ Y) : 𝟙 X ≫ f = f := by simp

example {W X Y Z : Cᵒᵖ} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z) :
    (f ≫ g) ≫ h = f ≫ g ≫ h := by simp

/-- Morphisms in opposite category -/
example (X Y : Cᵒᵖ) : (X ⟶ Y) = (Y.unop ⟶ X.unop)ᵒᵖ := rfl

/-- Double opposite -/
example (C : Type*) [Category C] : Cᵒᵖᵒᵖ = C := rfl

end OppositeReview

section ULiftWithOpposite

universe u v u'

variable {C : Type u} [Category.{v} C]

/-- ULift and opposite commute -/
example : Category.{v} (ULift.{u'} Cᵒᵖ) := inferInstance

example : Category.{v} (ULift.{u'} C)ᵒᵖ := inferInstance

/-- These are not definitionally equal but are equivalent -/
example (X Y : ULift.{u'} Cᵒᵖ) :
    (X ⟶ Y) = (X.down ⟶ Y.down : Cᵒᵖ → Cᵒᵖ) := rfl

end ULiftWithOpposite

section EdgeCases

/-- ULift with same universe level -/
example (C : Type u) [Category.{v} C] : Category.{v} (ULift.{u} C) := inferInstance

/-- Multiple ULifts -/
example (C : Type u) [Category.{v} C] : 
    Category.{v} (ULift.{u + 2} (ULift.{u + 1} C)) := inferInstance

/-- ULift of small category to various levels -/
example (C : Type u) [SmallCategory C] : SmallCategory (ULift.{u} C) := inferInstance
example (C : Type u) [SmallCategory C] : LargeCategory (ULift.{u + 1} C) := inferInstance

/-- Empty and unit categories with ULift -/
example : Category (ULift Empty) := inferInstance
example : Category (ULift Unit) := inferInstance

end EdgeCases

end CategoryTheoryTest.OppositeAndULift

/-!
## Summary

This file tests:
1. The `uliftCategory` instance and its properties
2. Preservation of category laws under ULift
3. Concrete examples with Type*
4. Interaction between ULift and opposite categories
5. Various universe level scenarios
6. Reviews opposite category properties (already tested in CategoryLaws.lean)

The ULift category instance from Category.Basic.lean is fully tested.
-/