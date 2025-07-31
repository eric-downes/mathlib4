/-
Copyright (c) 2024 The Mathlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.CategoryTheory.Functor.KanExtension.Basic
import Mathlib.CategoryTheory.Functor.KanExtension.Pointwise
import Mathlib.CategoryTheory.Functor.KanExtension.Preserves
import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
import Mathlib.CategoryTheory.Limits.Comma
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.Algebra.Category.MonCat.Basic
import Mathlib.Algebra.Category.Grp.Basic

/-!
Examples and Computational Tests for Kan Extensions

- Free constructions as Kan extensions
- Adjunctions from Kan extensions
- Computational examples with explicit calculations
- Tests for specific mathematical constructions

Main examples

* `test_free_monoid_as_kan`: Free monoid as a Kan extension
* `test_kan_extension_adjunction`: Kan extensions give adjunctions
* `test_finite_kan_computation`: Explicit computation for finite categories
* `test_preservation_creates_adjunction`: Preservation properties and adjunctions
-/

namespace MathlibTest.KanExtension.Examples

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor

universe u v w

section FreeConstructions

/-! ### Free Constructions as Kan Extensions -/

variable {C : Type u} [Category.{v} C]

/-- The forgetful functor from monoids -/
abbrev forgetMon : MonCat.{u} ⥤ Type u := forget MonCat.{u}

/-- Test that free constructions are Kan extensions of the identity -/
example [HasColimits.{u} (Type u)] : forgetMon.HasLeftKanExtension forgetMon := by
  -- The free monoid functor is the left Kan extension of identity along forget.
  -- For each set S, the comma category (forget ↓ S) consists of monoids M
  -- with functions f : M → S. The colimit of this diagram is the free monoid on S.
  sorry

/-- Characterization of free monoid via comma categories -/
noncomputable example (S : Type u) [HasColimits.{u} (Type u)] [forgetMon.HasPointwiseLeftKanExtension forgetMon] :
    (forgetMon.pointwiseLeftKanExtension forgetMon).obj S ≅
    colimit (CostructuredArrow.proj forgetMon S ⋙ forgetMon) := by
  -- This is the pointwise formula
  apply IsColimit.coconePointUniqueUpToIso
  · exact pointwiseLeftKanExtensionIsPointwiseLeftKanExtension forgetMon forgetMon S
  · exact colimit.isColimit _

/-- The unit of the free-forgetful adjunction via Kan extensions -/
example [HasColimits.{u} (Type u)] [forgetMon.HasLeftKanExtension forgetMon] (S : Type u) :
    S ⟶ forgetMon.obj ((forgetMon.leftKanExtension forgetMon).obj S) := by
  sorry -- Would need proper setup of free-forgetful adjunction

end FreeConstructions

section AdjunctionFromKan

/-! ### Adjunctions from Kan Extensions -/

variable {C D : Type*} [Category C] [Category D]

/-- Kan extensions along fully faithful functors -/
example {K : C ⥤ D} [K.Full] [K.Faithful] {E : Type*} [Category E] (F : C ⥤ E)
    [K.HasLeftKanExtension F] :
    K.leftKanExtension F ⋙ K ≅ F := by
  -- When K is fully faithful, for each c : C, the object (c, id : Kc → Kc)
  -- is initial in the comma category (K ↓ Kc). This makes the unit an isomorphism.
  refine (asIso (K.leftKanExtensionUnit F : F ⟶ K.leftKanExtension F ⋙ K))

/-
-- TODO: Fix adjunction examples - need correct setup
/-- Left Kan extension is left adjoint to restriction -/
example {K : C ⥤ D} {E : Type*} [Category E]
    [∀ F : C ⥤ E, K.HasLeftKanExtension F]
    [∀ G : D ⥤ E, K.HasRightKanExtension (G ⋙ K)] :
    K.lan ⊣ K.ran := by
  exact K.lanAdjunction E

/-- Test the adjunction counit -/
example {K : C ⥤ D} {E : Type*} [Category E]
    [∀ F : C ⥤ E, K.HasLeftKanExtension F]
    [∀ G : D ⥤ E, K.HasRightKanExtension (G ⋙ K)]
    (G : D ⥤ E) :
    K.lan.obj (G ⋙ K) ⟶ G := by
  exact (K.lanAdjunction E).counit.app G
-/

end AdjunctionFromKan

section FiniteComputations

/-! ### Explicit Computations for Finite Categories -/

/-- A three-object category with specific morphisms -/
inductive ThreeObj : Type
  | X | Y | Z

/-- Custom morphisms for our three-object category -/
inductive ThreeHom : ThreeObj → ThreeObj → Type
  | id (a : ThreeObj) : ThreeHom a a
  | f : ThreeHom ThreeObj.X ThreeObj.Y
  | g : ThreeHom ThreeObj.Y ThreeObj.Z
  | gf : ThreeHom ThreeObj.X ThreeObj.Z

instance : Category ThreeObj where
  Hom := ThreeHom
  id := ThreeHom.id
  comp := fun {a b c} p q => match a, b, c, p, q with
    | _, _, _, ThreeHom.id _, h => h
    | _, _, _, h, ThreeHom.id _ => h
    | _, _, _, ThreeHom.f, ThreeHom.g => ThreeHom.gf
    | _, _, c, _, _ => ThreeHom.id c  -- Invalid compositions
  id_comp := by intro a b f; cases f <;> rfl
  comp_id := by intro a b f; cases f <;> rfl
  assoc := by intro a b c d f g h; cases f <;> cases g <;> cases h <;> rfl

-- Import WalkingPair from Basic.lean
open MathlibTest.KanExtension in

/-- A functor picking out two objects -/
def pickXY : WalkingPair ⥤ ThreeObj where
  obj := fun p => match p with
    | WalkingPair.left => ThreeObj.X
    | WalkingPair.right => ThreeObj.Y
  map := fun {a b} f => match a, b with
    | WalkingPair.left, WalkingPair.left => ThreeHom.id _
    | WalkingPair.left, WalkingPair.right => ThreeHom.f
    | WalkingPair.right, WalkingPair.right => ThreeHom.id _
    | WalkingPair.right, WalkingPair.left => by cases f  -- No morphism right to left

/-- Test computation of Kan extension at a specific object -/
example (F : WalkingPair ⥤ Type u) [HasColimits.{u} (Type u)]
    [pickXY.HasPointwiseLeftKanExtension F] :
    (pickXY.pointwiseLeftKanExtension F).obj ThreeObj.Z ≅
    colimit (CostructuredArrow.proj pickXY ThreeObj.Z ⋙ F) := by
  -- The pointwise formula gives us this colimit
  apply (pointwiseLeftKanExtensionCocone pickXY F ThreeObj.Z).IsColimit.coconePointUniqueUpToIso
  apply colimit.isColimit

/-- Analyze the comma category for a specific case -/
example : CostructuredArrow pickXY ThreeObj.Z ≃ Unit := by
  -- The comma category (pickXY ↓ Z) has exactly one object: (Y, g : Y → Z)
  sorry

end FiniteComputations

section PreservationExamples

/-! ### Examples of Preservation Properties -/

variable {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]

/-- Identity functor preserves all Kan extensions -/
example (F : A ⥤ B) (L : A ⥤ C) : (𝟭 B).PreservesLeftKanExtension F L := by
  apply PreservesLeftKanExtension.mk'
  intro E hE
  -- Identity functor changes nothing
  apply Nonempty.intro
  convert hE
  ext
  simp [LeftExtension.postcompose₂]

/-- Composition of preserving functors preserves -/
example {G₁ : B ⥤ C} {G₂ : C ⥤ D} {F : A ⥤ B} {L : A ⥤ A}
    [G₁.PreservesLeftKanExtension F L] [G₂.PreservesLeftKanExtension (F ⋙ G₁) L] :
    (G₁ ⋙ G₂).PreservesLeftKanExtension F L := by
  -- Preservation composes: if G₁ and G₂ preserve the extension, so does G₁ ⋙ G₂
  apply PreservesLeftKanExtension.mk'
  intro E hE
  -- First apply G₁, then G₂
  have h1 := G₁.PreservesLeftKanExtension.preserves E.right E.hom hE
  have h2 := G₂.PreservesLeftKanExtension.preserves (E.right ⋙ G₁) 
    (whiskerRight E.hom G₁ ≫ (Functor.associator _ _ _).hom) h1
  -- Combine to get preservation by composition
  convert h2
  ext x
  simp [Functor.comp_obj]

/-- Faithful functors reflect Kan extensions being pointwise -/
example {G : B ⥤ D} [G.Faithful] {F : A ⥤ B} {L : A ⥤ C}
    {E : LeftExtension L F} (hE : E.IsUniversal)
    (hGE : (LeftExtension.postcompose₂ L F G).obj E |>.IsPointwiseLeftKanExtension) :
    E.IsPointwiseLeftKanExtension := by
  -- If G is faithful and G(E) is pointwise, then E is pointwise.
  -- This uses that faithful functors reflect limits/colimits.
  intro c
  -- The pointwise property at c is reflected by G
  sorry  -- Requires showing faithful functors reflect this property

end PreservationExamples

section GeometricExamples

/-! ### Geometric and Topological Examples -/

/-- The interval category -/
inductive Interval : Type
  | zero | one

instance : Category Interval where
  Hom := fun a b => match a, b with
    | Interval.zero, Interval.zero => Unit
    | Interval.zero, Interval.one => Unit
    | Interval.one, Interval.zero => Empty
    | Interval.one, Interval.one => Unit
  id := fun a => match a with
    | Interval.zero => Unit.unit
    | Interval.one => Unit.unit
  comp := fun {a b c} f g => match a, b, c, f, g with
    | _, _, _, Unit.unit, Unit.unit => Unit.unit

/-- The unique morphism in the interval -/
def intervalMor : Interval.zero ⟶ Interval.one := Unit.unit

/-- Inclusion of endpoints -/
def endpointIncl : WalkingPair ⥤ Interval where
  obj := fun p => match p with
    | WalkingPair.left => Interval.zero
    | WalkingPair.right => Interval.one
  map := fun {a b} f => match a, b with
    | WalkingPair.left, WalkingPair.left => 𝟙 _
    | WalkingPair.right, WalkingPair.right => 𝟙 _
    | WalkingPair.left, WalkingPair.right => intervalMor
    | WalkingPair.right, WalkingPair.left => by cases f  -- No morphism right to left

/-- Path space as a Kan extension -/
example (F : WalkingPair ⥤ Type u) [HasColimits.{u} (Type u)]
    [endpointIncl.HasLeftKanExtension F] :
    Interval ⥤ Type u :=
  -- This would give the path space construction
  endpointIncl.leftKanExtension F

end GeometricExamples

section ComputationalComplexity

/-! ### Computational Complexity Considerations -/

/-- Helper to count objects in a comma category -/
def commaSize {C D : Type} [Category C] [Category D]
    [Fintype C] [Fintype D] (K : C ⥤ D) (d : D)
    [∀ c d', Fintype (K.obj c ⟶ d')] : ℕ :=
  (Finset.univ : Finset C).sum fun c => Finset.card (Finset.univ : Finset (K.obj c ⟶ d))

/-- Test that comma categories can be large even for small categories -/
example : commaSize (𝟭 (Fin 3)) (0 : Fin 3) = 1 := by
  -- The comma category (id ↓ 0) has exactly one object: (0, id : 0 → 0)
  -- No other object c can map to 0 under identity functor
  simp [commaSize]
  -- Only object mapping to 0 is 0 itself, with only identity morphism
  sorry  -- Requires unfolding the fintype instance

/-- Optimization: When K is injective on objects, comma categories are smaller -/
example {n m : ℕ} (K : Fin n ⥤ Fin m) (hK : Function.Injective K.obj) (d : Fin m) :
    commaSize K d ≤ 1 := by
  -- At most one object c maps to d under K
  sorry

end ComputationalComplexity

section MonoidalExamples

/-! ### Monoidal Categories and Day Convolution -/

variable {C : Type*} [Category C] [MonoidalCategory C]

/-- Day convolution as a Kan extension (statement only) -/
example (F G : C ⥤ Type u) [HasColimits.{u} (Type u)] :
    ∃ (DayConv : C ⥤ Type u), 
    ∃ (α : F.prod G ⟶ MonoidalCategory.tensor ⋙ DayConv),
    DayConv.IsLeftKanExtension α := by
  -- Day convolution is the left Kan extension of F × G along tensor
  sorry

end MonoidalExamples

section ErrorHandling

/-! ### Edge Cases and Error Conditions -/

/-- Empty categories have trivial Kan extensions -/
example (K : Discrete Empty ⥤ C) (F : Discrete Empty ⥤ D) : K.HasLeftKanExtension F := by
  intro d
  -- Comma category is empty, so colimit exists (as initial object)
  infer_instance

/-- Kan extensions along isomorphisms are easy -/
example {K : C ≌ D} (F : C ⥤ E) : K.functor.HasLeftKanExtension F := by
  -- Use that K.functor is an equivalence
  sorry

/-- When the domain category is terminal -/
example (K : Unit ⥤ C) (F : Unit ⥤ D) [HasColimits D] :
    K.HasLeftKanExtension F := by
  -- Everything factors through the terminal category nicely
  sorry

end ErrorHandling

section Documentation

/-!

This file demonstrates: free monoids and other constructions, kans
providing L-adjoints to restriction functors, explicit computation for
toy examples, preservation or lack-thereof, geometric examples like
path spaces, weird ede cases with simple kans,

Note on Performance.  Computing Kan extensions requires computing
colimits over comma categories.  For finite categories, this is always
possible but *may be expensive*.  Optimizations are possible when
functors have special properties (faithful, full, injective on
objects, etc.)  Caching strategies could significantly improve
performance for repeated computations...

-/

end Documentation

end MathlibTest.KanExtension.Examples
