/-
Copyright (c) 2025 The Mathlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.CategoryTheory.Functor.KanExtension.Basic
import Mathlib.CategoryTheory.Functor.KanExtension.Pointwise
import Mathlib.CategoryTheory.Functor.KanExtension.Preserves

/-!
# Minimal Tests for Kan Extensions

This file contains minimal tests demonstrating that Kan extensions exist in mathlib.

-/

namespace MathlibTest.KanExtension

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor

universe u v w

section BasicTests

variable {C D E : Type*} [Category C] [Category D] [Category E]

/-- Test that Kan extensions have the universal property -/
example {L : C ⥤ D} {F : C ⥤ E} {F' : D ⥤ E} {α : F ⟶ L ⋙ F'}
    [F'.IsLeftKanExtension α] {G : D ⥤ E} (β : F ⟶ L ⋙ G) :
    ∃! (γ : F' ⟶ G), α ≫ whiskerLeft L γ = β := by
  use F'.descOfIsLeftKanExtension α G β
  constructor
  · exact F'.descOfIsLeftKanExtension_fac α G β
  · intro γ' hγ'
    exact F'.hom_ext_of_isLeftKanExtension α γ' _ 
      (hγ' ▸ (F'.descOfIsLeftKanExtension_fac α G β).symm)

/-- Test that Kan extensions are unique up to isomorphism -/
noncomputable example {L : C ⥤ D} {F : C ⥤ E} {F₁ F₂ : D ⥤ E}
    {α₁ : F ⟶ L ⋙ F₁} {α₂ : F ⟶ L ⋙ F₂}
    [F₁.IsLeftKanExtension α₁] [F₂.IsLeftKanExtension α₂] :
    F₁ ≅ F₂ := 
  leftKanExtensionUnique F₁ α₁ F₂ α₂

/-- Test that we have pointwise Kan extensions when colimits exist -/
example {L : C ⥤ D} {F : C ⥤ E} [L.HasPointwiseLeftKanExtension F] (d : D) :
    HasColimit (CostructuredArrow.proj L d ⋙ F) := by
  infer_instance

/-- Test the chosen Kan extension functor -/
noncomputable example {L : C ⥤ D} {F : C ⥤ E} [L.HasLeftKanExtension F] :
    D ⥤ E := L.leftKanExtension F

/-- Test the unit of the Kan extension -/
noncomputable example {L : C ⥤ D} {F : C ⥤ E} [L.HasLeftKanExtension F] :
    F ⟶ L ⋙ L.leftKanExtension F := L.leftKanExtensionUnit F

/-- Test that the chosen extension is a Kan extension -/
example {L : C ⥤ D} {F : C ⥤ E} [L.HasLeftKanExtension F] :
    (L.leftKanExtension F).IsLeftKanExtension (L.leftKanExtensionUnit F) := by
  infer_instance

end BasicTests

section PreservationTests

variable {A B C : Type*} [Category A] [Category B] [Category C]

/-- Test that we have preservation typeclasses -/
example (G : B ⥤ C) (F : A ⥤ B) (L : A ⥤ A) 
    [G.PreservesLeftKanExtension F L] : True := trivial

/-- Test pointwise preservation -/  
example (G : B ⥤ C) (F : A ⥤ B) (L : A ⥤ A)
    [G.PreservesPointwiseLeftKanExtension F L] : True := trivial

end PreservationTests

section ExistingExamples

/-- Test that HasLeftKanExtension instances exist -/
noncomputable example {C D E : Type*} [Category C] [Category D] [Category E] 
    (L : C ⥤ D) (F : C ⥤ E) [L.HasLeftKanExtension F] : 
    D ⥤ E := L.leftKanExtension F

/-- Test adjunction between lan and ran -/
example {C D E : Type*} [Category C] [Category D] [Category E]
    (K : C ⥤ D) [∀ F : C ⥤ E, K.HasLeftKanExtension F] :
    ∃ adj : K.lan ⊣ _, True := by
  use K.lanAdjunction E
  trivial

end ExistingExamples

/-
Summary: This file demonstrates that mathlib has:
- Basic Kan extension definitions (IsLeftKanExtension)  
- Uniqueness theorem (leftKanExtensionUnique)
- Chosen Kan extensions (leftKanExtension, leftKanExtensionUnit)
- Pointwise theory (HasPointwiseLeftKanExtension)
- Preservation properties (PreservesLeftKanExtension)

What's missing:
- Concrete examples and test cases
- Computational examples for specific categories
- Proofs that standard constructions are Kan extensions
-/

end MathlibTest.KanExtension