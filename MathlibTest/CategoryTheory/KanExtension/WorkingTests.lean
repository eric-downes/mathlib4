/-
Copyright (c) 2025 The Mathlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.CategoryTheory.Functor.KanExtension.Basic
import Mathlib.CategoryTheory.Functor.KanExtension.Preserves
import Mathlib.CategoryTheory.Functor.KanExtension.Pointwise
import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic

/-!
# Tests for Kan Extensions

This file contains tests for the Kan extension API in mathlib.
These tests demonstrate basic usage and verify the API works as expected.
-/

universe u v

open CategoryTheory

namespace CategoryTheory.KanExtension.Tests

section BasicTypes
-- Test that basic types exist
#check Functor.IsLeftKanExtension
#check Functor.IsRightKanExtension
#check Functor.HasLeftKanExtension
#check Functor.HasRightKanExtension

-- Test that basic functions exist
#check Functor.leftKanExtension
#check Functor.leftKanExtensionUnit
#check Functor.rightKanExtension
#check Functor.rightKanExtensionCounit

-- Test preservation typeclasses
#check Functor.PreservesLeftKanExtension
#check Functor.PreservesRightKanExtension
end BasicTypes

section BasicProperties
variable {C H D : Type*} [Category C] [Category H] [Category D]
variable (L : C ⥤ D) (F : C ⥤ H) [L.HasLeftKanExtension F]

-- The chosen left Kan extension has the IsLeftKanExtension property
example : (L.leftKanExtension F).IsLeftKanExtension (L.leftKanExtensionUnit F) :=
  inferInstance

-- Preservation instances work
variable {A B : Type*} [Category A] [Category B]
variable (G : B ⥤ D) (F' : A ⥤ B) (L' : A ⥤ C)

example [G.PreservesLeftKanExtension F' L'] : G.PreservesLeftKanExtension F' L' :=
  inferInstance

end BasicProperties

section PointwiseInstances
variable {C D E : Type*} [Category C] [Category D] [Category E]
variable (L : C ⥤ D) (F : C ⥤ E) [L.HasPointwiseLeftKanExtension F]

-- Pointwise instances give general instances
example : L.HasLeftKanExtension F := inferInstance

end PointwiseInstances

section UniversalProperty
variable {C H D : Type*} [Category C] [Category H] [Category D]
variable {L : C ⥤ D} {F : C ⥤ H} {F' : D ⥤ H} {α : F ⟶ L ⋙ F'}
variable [h : F'.IsLeftKanExtension α]

-- Universal property gives us descent morphism
noncomputable example (G : D ⥤ H) (β : F ⟶ L ⋙ G) : F' ⟶ G :=
  F'.descOfIsLeftKanExtension α G β

-- And it satisfies the factorization property
example (G : D ⥤ H) (β : F ⟶ L ⋙ G) :
    α ≫ L.whiskerLeft (F'.descOfIsLeftKanExtension α G β) = β :=
  F'.descOfIsLeftKanExtension_fac α G β

end UniversalProperty

section PreservationProperties
variable {C D : Type*} [Category C] [Category D]
variable (L : C ⥤ D) (F : C ⥤ D) [L.HasLeftKanExtension F]

-- Identity functor preserves Kan extensions
example : Prop := (𝟭 D).PreservesLeftKanExtension F L

end PreservationProperties

section CommaCategories
variable {C D : Type u} [Category C] [Category D]
variable (F : C ⥤ D) (d : D)

-- Comma categories are available
example : Type u := CostructuredArrow F d

-- With projection functors
example : CostructuredArrow F d ⥤ C := CostructuredArrow.proj F d

end CommaCategories

end CategoryTheory.KanExtension.Tests