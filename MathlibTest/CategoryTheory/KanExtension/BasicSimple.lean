/-
Copyright (c) 2025 The Mathlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.CategoryTheory.Functor.KanExtension.Basic
import Mathlib.CategoryTheory.Functor.KanExtension.Pointwise
import Mathlib.CategoryTheory.Functor.KanExtension.Preserves
import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
import Mathlib.CategoryTheory.Limits.Shapes.Terminal
import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic

/-!
# Simple Tests for Kan Extensions

This file contains basic tests for the Kan extension API in mathlib.

## Main tests

* Universal property of Kan extensions
* Uniqueness up to isomorphism
* Pointwise formula using colimits
* Basic preservation properties
-/

namespace MathlibTest.KanExtension

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor

universe u v w

section BasicTests

variable {C D E : Type*} [Category C] [Category D] [Category E]

/-- Test that Kan extensions satisfy the universal property -/
example {L : C ⥤ D} {F : C ⥤ E} {F' : D ⥤ E} {α : F ⟶ L ⋙ F'}
    [F'.IsLeftKanExtension α] {G : D ⥤ E} (β : F ⟶ L ⋙ G) :
    ∃! (γ : F' ⟶ G), α ≫ whiskerLeft L γ = β := by
  use F'.descOfIsLeftKanExtension α G β
  constructor
  · exact F'.descOfIsLeftKanExtension_fac α G β
  · intro γ' hγ'
    exact F'.hom_ext_of_isLeftKanExtension α γ' _ 
      (hγ' ▸ (F'.descOfIsLeftKanExtension_fac α G β).symm)

/-- Test uniqueness of Kan extensions -/
noncomputable example {L : C ⥤ D} {F : C ⥤ E} {F₁ F₂ : D ⥤ E}
    {α₁ : F ⟶ L ⋙ F₁} {α₂ : F ⟶ L ⋙ F₂}
    [F₁.IsLeftKanExtension α₁] [F₂.IsLeftKanExtension α₂] :
    F₁ ≅ F₂ := 
  leftKanExtensionUnique F₁ α₁ F₂ α₂

end BasicTests

section PointwiseTests

variable {C D E : Type*} [Category C] [Category D] [Category E]

/-- Test that pointwise Kan extensions exist when we have colimits -/
example {L : C ⥤ D} {F : C ⥤ E} [L.HasPointwiseLeftKanExtension F] (d : D) :
    HasColimit (CostructuredArrow.proj L d ⋙ F) := by
  infer_instance

/-- Test the colimit formula for pointwise Kan extensions -/
noncomputable example {L : C ⥤ D} {F : C ⥤ E} 
    [L.HasPointwiseLeftKanExtension F] (d : D) :
    (L.pointwiseLeftKanExtension F).obj d ≅ 
    colimit (CostructuredArrow.proj L d ⋙ F) := by
  apply IsColimit.coconePointUniqueUpToIso
  · exact (pointwiseLeftKanExtensionIsPointwiseLeftKanExtension L F d)
  · exact colimit.isColimit _

end PointwiseTests

section PreservationTests

variable {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]

/-- Identity functor preserves all Kan extensions -/
example (F : A ⥤ B) (L : A ⥤ C) : (𝟭 B).PreservesLeftKanExtension F L := by
  apply PreservesLeftKanExtension.mk'
  intro E hE
  apply Nonempty.intro
  convert hE
  ext
  simp [LeftExtension.postcompose₂]

/-- Test preservation creates instance -/
example {G : B ⥤ D} {F : A ⥤ B} {L : A ⥤ C}
    [∀ c, PreservesColimit (CostructuredArrow.proj L c ⋙ F) G] :
    G.PreservesPointwiseLeftKanExtension F L := by
  intro c
  infer_instance

end PreservationTests

section SimpleExamples

/-- A basic two-element type -/
inductive Two : Type
  | zero | one

/-- Two has two morphisms and identities -/
instance : Category Two where
  Hom := fun a b => if a = Two.zero ∧ b = Two.one then Unit else if a = b then Unit else Empty
  id := fun _ => by simp [Hom]
  comp := fun {a b c} f g => by
    simp only [Hom] at f g ⊢
    split_ifs <;> try exact Unit.unit <;> try (cases f) <;> try (cases g)
  id_comp := by intro a b f; simp [Hom] at f ⊢; split_ifs at f ⊢ <;> try cases f <;> rfl
  comp_id := by intro a b f; simp [Hom] at f ⊢; split_ifs at f ⊢ <;> try cases f <;> rfl
  assoc := by 
    intro a b c d f g h
    simp [Hom] at f g h ⊢
    split_ifs at f g h ⊢ <;> try cases f <;> try cases g <;> try cases h <;> rfl

/-- Test that we can form comma categories -/
example : CostructuredArrow (𝟭 Two) Two.one ⥤ Two :=
  CostructuredArrow.proj (𝟭 Two) Two.one

end SimpleExamples

end MathlibTest.KanExtension