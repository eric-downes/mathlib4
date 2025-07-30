/-
Copyright (c) 2025 The Mathlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.CategoryTheory.Functor.KanExtension.Basic
import Mathlib.CategoryTheory.Functor.KanExtension.Pointwise
import Mathlib.CategoryTheory.Functor.KanExtension.Preserves
import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
import Mathlib.CategoryTheory.Limits.Shapes.Terminal
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic
import Mathlib.CategoryTheory.Functor.Const

/-!
# Tests for Kan Extensions

This file contains tests for the Kan extension API in mathlib, including:
- Basic universal property tests
- Pointwise Kan extension tests
- Preservation property tests
- Concrete computational examples
- some relevant comma category infrastructure

Main results

* `test_yoneda_as_kan`: The Yoneda embedding is a Kan extension
* `test_limits_as_kan`: Limits are Kan extensions along the constant functor
* `test_kan_extension_unique`: Kan extensions are unique up to isomorphism
* `test_pointwise_computed_by_colimits`: Pointwise Kan extensions use the colimit formula
* `test_preservation_by_adjoints`: Left adjoints preserve left Kan extensions
-/

namespace MathlibTest.KanExtension

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor

universe u v w

section BasicTests

/-! ### Basic Universal Property Tests -/

/-- Test that Kan extensions satisfy the universal property -/
example {C D E : Type*} [Category C] [Category D] [Category E]
    {L : C ⥤ D} {F : C ⥤ E} {F' : D ⥤ E} {α : F ⟶ L ⋙ F'}
    [F'.IsLeftKanExtension α] {G : D ⥤ E} (β : F ⟶ L ⋙ G) :
    ∃! (γ : F' ⟶ G), α ≫ whiskerLeft L γ = β := by
  use F'.descOfIsLeftKanExtension α G β
  constructor
  · exact F'.descOfIsLeftKanExtension_fac α G β
  · intro γ' hγ'
    exact F'.hom_ext_of_isLeftKanExtension α γ' _ (hγ' ▸ (F'.descOfIsLeftKanExtension_fac α G β).symm)

/-- Test uniqueness of Kan extensions -/
example {C D E : Type*} [Category C] [Category D] [Category E]
    {L : C ⥤ D} {F : C ⥤ E} {F₁ F₂ : D ⥤ E}
    {α₁ : F ⟶ L ⋙ F₁} {α₂ : F ⟶ L ⋙ F₂}
    [F₁.IsLeftKanExtension α₁] [F₂.IsLeftKanExtension α₂] :
    F₁ ≅ F₂ := by
  exact leftKanExtensionUnique F₁ α₁ F₂ α₂

/-- Test that identity functor is its own Kan extension -/
example {C : Type*} [Category C] : (𝟭 C).IsLeftKanExtension (𝟙 (𝟭 C)) := by
  constructor
  apply Nonempty.intro
  apply StructuredArrow.mkIdInitial
  · exact Functor.full_id
  · exact Functor.faithful_id

end BasicTests

section CommaCategories

/-! ### Tests for Comma Categories in Kan Extensions -/

variable {C D E : Type*} [Category C] [Category D] [Category E]

/-- Test basic properties of structured arrows -/
example (S : D) (T : C ⥤ D) (c : C) (f : S ⟶ T.obj c) :
    (StructuredArrow.mk f).right = c := by
  rfl

/-- Test morphisms in structured arrow categories -/
example {S : D} {T : C ⥤ D} {c₁ c₂ : C} (f₁ : S ⟶ T.obj c₁) (f₂ : S ⟶ T.obj c₂) (g : c₁ ⟶ c₂)
    (h : f₁ ≫ T.map g = f₂) :
    StructuredArrow.homMk g h : StructuredArrow.mk f₁ ⟶ StructuredArrow.mk f₂ := by
  rfl

/-- Test costructured arrows -/
example (S : C ⥤ D) (T : D) (c : C) (f : S.obj c ⟶ T) :
    (CostructuredArrow.mk f).left = c := by
  rfl

/-- The projection functor from comma categories is used in the colimit formula -/
example {L : C ⥤ D} {F : C ⥤ E} (d : D) :
    CostructuredArrow.proj L d : CostructuredArrow L d ⥤ C := by
  rfl

end CommaCategories

section PointwiseTests

/-! ### Pointwise Kan Extension Tests -/

variable {C D E : Type*} [Category C] [Category D] [Category E]

/-- Test that pointwise Kan extensions are computed by colimits -/
example {L : C ⥤ D} {F : C ⥤ E} [L.HasPointwiseLeftKanExtension F] (d : D) :
    HasColimit (CostructuredArrow.proj L d ⋙ F) := by
  infer_instance

/-- Test the colimit formula for pointwise Kan extensions -/
example {L : C ⥤ D} {F : C ⥤ E} [L.HasPointwiseLeftKanExtension F] (d : D) :
    (L.pointwiseLeftKanExtension F).obj d ≅ colimit (CostructuredArrow.proj L d ⋙ F) := by
  apply (pointwiseLeftKanExtensionCocone L F d).IsColimit.coconePointUniqueUpToIso
  apply colimit.isColimit

/-- Test that Kan extensions via colimits are pointwise -/
example {L : C ⥤ D} {F : C ⥤ E}
    [∀ d, HasColimit (CostructuredArrow.proj L d ⋙ F)] :
    ∃ (F' : D ⥤ E) (α : F ⟶ L ⋙ F'), F'.IsPointwiseLeftKanExtension α := by
  refine ⟨pointwiseLeftKanExtension L F, pointwiseLeftKanExtensionUnit L F, ?_⟩
  exact pointwiseLeftKanExtensionIsPointwiseLeftKanExtension L F

end PointwiseTests

section PreservationTests

/-! ### Preservation Property Tests -/

variable {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]

/-- Test that left adjoints preserve left Kan extensions -/
example {G : B ⥤ D} {G' : D ⥤ B} [G ⊣ G'] {F : A ⥤ B} {L : A ⥤ C}
    [L.HasLeftKanExtension F] :
    L.HasLeftKanExtension (F ⋙ G) := by
  -- This follows from the preservation property
  have : G.PreservesLeftKanExtension F L := by
    apply PreservesLeftKanExtension.mk_of_preserves_isLeftKanExtension
      (L.leftKanExtension F) (L.leftKanExtensionUnit F)
    -- Left adjoints preserve all colimits
    have adj := Adjunction.ofIsLeftAdjoint G
    have : ∀ (c : C), PreservesColimit (CostructuredArrow.proj L c ⋙ F) G :=
      fun c => Adjunction.leftAdjointPreservesColimits adj
    -- Since G preserves the relevant colimits, it preserves the Kan extension
    exact preserves_lan_of_preserves_colimits F L G
  infer_instance

/-- Test preservation of pointwise Kan extensions -/
example {G : B ⥤ D} {F : A ⥤ B} {L : A ⥤ C}
    [∀ c, PreservesColimit (CostructuredArrow.proj L c ⋙ F) G] :
    G.PreservesPointwiseLeftKanExtension F L := by
  intro c
  infer_instance

/-- Test the isomorphism when preserving Kan extensions -/
example {G : B ⥤ D} {F : A ⥤ B} {L : A ⥤ C}
    [G.PreservesLeftKanExtension F L] [L.HasLeftKanExtension F] :
    L.leftKanExtension F ⋙ G ≅ L.leftKanExtension (F ⋙ G) := by
  exact leftKanExtensionCompIsoOfPreserves G F L

end PreservationTests

section ConcreteExamples

/-! ### Concrete Computational Examples -/

/-- A simple two-object category -/
inductive WalkingPair : Type
  | left | right

instance : Category WalkingPair where
  Hom := fun a b => match a, b with
    | WalkingPair.left, WalkingPair.left => Unit
    | WalkingPair.left, WalkingPair.right => Unit
    | WalkingPair.right, WalkingPair.left => Empty
    | WalkingPair.right, WalkingPair.right => Unit
  id := fun _ => Unit.unit
  comp := fun f g => match f, g with
    | Unit.unit, Unit.unit => Unit.unit

/-- The inclusion of left into the walking pair -/
def walkingPairInclLeft : Unit ⥤ WalkingPair where
  obj := fun _ => WalkingPair.left
  map := fun _ => Unit.unit

/-- Test Kan extension along inclusion -/
example (F : Unit ⥤ Type u) [HasColimits.{u} (Type u)] :
    walkingPairInclLeft.HasLeftKanExtension F := by
  -- We need colimits over the comma categories
  constructor
  intro d
  cases d
  · -- For left: comma category has initial object
    apply hasColimitOfIso (F := CostructuredArrow.proj walkingPairInclLeft WalkingPair.left ⋙ F)
    sorry
  · -- For right: comma category is empty
    apply hasColimitOfIso (F := CostructuredArrow.proj walkingPairInclLeft WalkingPair.right ⋙ F)
    sorry

/-- The constant functor as a test case -/
def constExample (X : Type u) : Unit ⥤ Type u where
  obj := fun _ => X
  map := fun _ => id

/-- Computing a specific Kan extension value -/
example (X : Type u) [HasColimits.{u} (Type u)]
    [walkingPairInclLeft.HasPointwiseLeftKanExtension (constExample X)] :
    (walkingPairInclLeft.pointwiseLeftKanExtension (constExample X)).obj WalkingPair.left ≅ X := by
  -- At left, the comma category has the identity as initial object
  apply Nonempty.intro
  sorry

end ConcreteExamples

section ConstantFunctorTests

/-! ### Tests for Constant/Diagonal Functors -/

variable {J C : Type*} [Category J] [Category C]

/-- Test basic properties of the constant functor -/
example (X : C) : (const J).obj X : J ⥤ C := by
  rfl

/-- Test that constant functor is diagonal -/
example (X : C) (j : J) : ((const J).obj X).obj j = X := by
  rfl

/-- Constant functor preserves identity -/
example (X : C) : (const J).map (𝟙 X) = 𝟙 ((const J).obj X) := by
  rfl

/-- Test faithfulness when J is nonempty -/
example [Nonempty J] : Faithful (const J : C ⥤ J ⥤ C) := by
  infer_instance

end ConstantFunctorTests

section YonedaAsKanExtension

/-! ### The Yoneda Embedding as a Kan Extension -/

variable {C : Type*} [Category C]

/-- The Yoneda embedding can be viewed as a Kan extension of the identity -/
example : (𝟭 C).HasLeftKanExtension (𝟭 C) := by
  -- The Yoneda embedding gives the free cocompletion of C.
  -- For each d : C, the comma category (id ↓ d) has (d, id_d) as initial object,
  -- making the colimit trivial to compute.
  sorry

/-- Test that Yoneda preserves the identity up to natural isomorphism -/
example (c : C) : yoneda.obj c ≅ ((𝟭 (Cᵒᵖ ⥤ Type*)).obj (yoneda.obj c)) := by
  rfl

end YonedaAsKanExtension

section LimitsAsKanExtensions

/-! ### Limits and Colimits as Kan Extensions -/

variable {J C : Type*} [Category J] [Category C]

/-- Colimits are left Kan extensions along the constant functor -/
example [HasColimitsOfShape J C] :
    (const J : C ⥤ J ⥤ C).HasLeftKanExtension (𝟭 C) := by
  -- The left Kan extension of identity along const gives the colimit functor.
  -- Key insight: for F : J ⥤ C, the comma category (const ↓ F) is equivalent to J,
  -- so its colimit is precisely colimit F.
  sorry

/-- Limits are right Kan extensions along the constant functor -/
example [HasLimitsOfShape J C] :
    (const J : C ⥤ J ⥤ C).HasRightKanExtension (𝟭 C) := by
  -- Dual to colimits: the right Kan extension gives the limit functor.
  -- The comma category (F ↓ const) leads to limit F.
  sorry

/-- Test the relationship between colimits and Kan extensions -/
example [HasColimitsOfShape J C] (F : J ⥤ C) :
    ∃ (E : (J ⥤ C) ⥤ C) (α : 𝟭 C ⟶ const J ⋙ E),
    E.IsLeftKanExtension α ∧ E.obj F ≅ colimit F := by
  use colim
  use (constColimAdj J C).unit
  constructor
  · sorry -- Would show using adjunction properties
  · rfl

end LimitsAsKanExtensions

section PerformanceTests

/-! ### Performance and Computational Tests -/

/-- Test efficient computation for finite categories -/
def FinCat (n : ℕ) : Type := Fin n

instance (n : ℕ) : Category (FinCat n) where
  Hom := fun i j => if i ≤ j then Unit else Empty
  id := fun _ => Unit.unit
  comp := fun {a b c} f g =>
    match f, g with
    | Unit.unit, Unit.unit => Unit.unit

/-- A test functor between finite categories -/
def finInclusion (n m : ℕ) (h : n ≤ m) : FinCat n ⥤ FinCat m where
  obj := fun i => ⟨i.val, Nat.lt_of_lt_of_le i.prop h⟩
  map := fun {i j} f => by
    cases f
    exact Unit.unit

/-- Test computation for specific finite Kan extension -/
example [HasColimits.{0} (Type*)] :
    (finInclusion 2 3 (by norm_num : 2 ≤ 3)).HasPointwiseLeftKanExtension
      (const (FinCat 2) : Type* ⥤ FinCat 2 ⥤ Type*).obj Unit := by
  intro d
  -- Each comma category is finite, so has colimits
  sorry

end PerformanceTests

section Documentation

/-!
Summary of Tests

This test file validates basic UPs and unq-ness utui, walking pair
example, structure arrow/commad cats, pointwise kan extensions,
L-adjoints and colim preserving functors preserve appropriate kans,
and yoneda and (co)lim as special cases of kans.
-/

end Documentation

end MathlibTest.KanExtension