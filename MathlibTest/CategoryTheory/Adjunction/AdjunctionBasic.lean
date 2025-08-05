/-
Copyright (c) 2024 Mathlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: [Contributors]
-/
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Functor.Basic

/-!
# Core Tests for Adjunctions

This file tests essential APIs for adjunctions between functors.

## Coverage

- Basic adjunction structure and notation
- Unit and counit natural transformations
- Hom equivalence
- Triangle identities
- Basic constructors
-/

namespace CategoryTheoryTest.AdjunctionBasic

open CategoryTheory

noncomputable section

section BasicStructure

variable {C D : Type*} [Category C] [Category D]
variable {F : C ⥤ D} {G : D ⥤ C}

/-- Adjunction notation -/
example (adj : F ⊣ G) : Adjunction F G := adj

/-- Access unit of adjunction -/
example (adj : F ⊣ G) : 𝟭 C ⟶ F.comp G := adj.unit

/-- Access counit of adjunction -/
example (adj : F ⊣ G) : G.comp F ⟶ 𝟭 D := adj.counit

/-- Unit component at object -/
example (adj : F ⊣ G) (X : C) : X ⟶ G.obj (F.obj X) := adj.unit.app X

/-- Counit component at object -/
example (adj : F ⊣ G) (Y : D) : F.obj (G.obj Y) ⟶ Y := adj.counit.app Y

/-- Hom equivalence forward -/
example (adj : F ⊣ G) {X : C} {Y : D} (f : F.obj X ⟶ Y) : X ⟶ G.obj Y :=
  adj.homEquiv X Y f

/-- Hom equivalence backward -/
example (adj : F ⊣ G) {X : C} {Y : D} (g : X ⟶ G.obj Y) : F.obj X ⟶ Y :=
  (adj.homEquiv X Y).symm g

end BasicStructure

section TriangleIdentities

variable {C D : Type*} [Category C] [Category D]
variable {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)

/-- Left triangle identity components -/
example (X : C) : F.map (adj.unit.app X) ≫ adj.counit.app (F.obj X) = 𝟙 (F.obj X) :=
  adj.left_triangle_components X

/-- Right triangle identity components -/
example (Y : D) : adj.unit.app (G.obj Y) ≫ G.map (adj.counit.app Y) = 𝟙 (G.obj Y) :=
  adj.right_triangle_components Y

/-- Triangle identity in component form -/
example (X : C) : F.map (adj.unit.app X) ≫ adj.counit.app (F.obj X) = 𝟙 (F.obj X) := by
  simp

example (Y : D) : adj.unit.app (G.obj Y) ≫ G.map (adj.counit.app Y) = 𝟙 (G.obj Y) := by
  simp

end TriangleIdentities

section HomEquivProperties

variable {C D : Type*} [Category C] [Category D]
variable {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)

/-- Hom equiv is natural in first argument -/
example {X X' : C} {Y : D} (f : X' ⟶ X) (g : F.obj X ⟶ Y) :
    adj.homEquiv X' Y (F.map f ≫ g) = f ≫ adj.homEquiv X Y g := 
  adj.homEquiv_naturality_left f g

/-- Hom equiv is natural in second argument -/
example {X : C} {Y Y' : D} (f : F.obj X ⟶ Y) (g : Y ⟶ Y') :
    adj.homEquiv X Y' (f ≫ g) = adj.homEquiv X Y f ≫ G.map g := 
  adj.homEquiv_naturality_right f g

/-- Hom equiv round trip -/
example {X : C} {Y : D} (f : F.obj X ⟶ Y) :
    (adj.homEquiv X Y).symm (adj.homEquiv X Y f) = f := by
  simp

example {X : C} {Y : D} (g : X ⟶ G.obj Y) :
    adj.homEquiv X Y ((adj.homEquiv X Y).symm g) = g := by
  simp

end HomEquivProperties

section Constructors

variable {C D : Type*} [Category C] [Category D]
variable (F : C ⥤ D) (G : D ⥤ C)

/-- Construct adjunction from hom equivalence -/
example (homEquiv : ∀ X Y, (F.obj X ⟶ Y) ≃ (X ⟶ G.obj Y))
    (homEquiv_naturality_left_symm : ∀ {X' X Y} (f : X' ⟶ X) (g : X ⟶ G.obj Y),
      (homEquiv X' Y).symm (f ≫ g) = F.map f ≫ (homEquiv X Y).symm g)
    (homEquiv_naturality_right : ∀ {X Y Y'} (f : F.obj X ⟶ Y) (g : Y ⟶ Y'),
      homEquiv X Y' (f ≫ g) = homEquiv X Y f ≫ G.map g) :
    F ⊣ G :=
  Adjunction.mkOfHomEquiv
    { homEquiv := homEquiv
      homEquiv_naturality_left_symm := homEquiv_naturality_left_symm
      homEquiv_naturality_right := homEquiv_naturality_right }


end Constructors

section Composition

variable {C D E : Type*} [Category C] [Category D] [Category E]
variable {F : C ⥤ D} {G : D ⥤ C} {F' : D ⥤ E} {G' : E ⥤ D}

/-- Composition of adjunctions -/
example (adj1 : F ⊣ G) (adj2 : F' ⊣ G') : F ⋙ F' ⊣ G' ⋙ G :=
  adj1.comp adj2


end Composition

section TypeclassInstances

variable {C D : Type*} [Category C] [Category D]

/-- IsLeftAdjoint instance -/
example (F : C ⥤ D) [h : F.IsLeftAdjoint] : ∃ G, Nonempty (F ⊣ G) := by
  use F.rightAdjoint
  exact ⟨Adjunction.ofIsLeftAdjoint F⟩

/-- IsRightAdjoint instance -/
example (G : D ⥤ C) [h : G.IsRightAdjoint] : ∃ F, Nonempty (F ⊣ G) := by
  use G.leftAdjoint
  exact ⟨Adjunction.ofIsRightAdjoint G⟩

/-- Extract adjunction from IsLeftAdjoint -/
example (F : C ⥤ D) [h : F.IsLeftAdjoint] : F ⊣ F.rightAdjoint :=
  Adjunction.ofIsLeftAdjoint F

/-- Extract adjunction from IsRightAdjoint -/
example (G : D ⥤ C) [h : G.IsRightAdjoint] : G.leftAdjoint ⊣ G :=
  Adjunction.ofIsRightAdjoint G

end TypeclassInstances

section IdentityAdjunction

variable {C : Type*} [Category C]

/-- Identity functor is self-adjoint -/
example : 𝟭 C ⊣ 𝟭 C := Adjunction.id

/-- Unit of identity adjunction -/
example : (Adjunction.id : 𝟭 C ⊣ 𝟭 C).unit = 𝟙 (𝟭 C) := rfl

/-- Counit of identity adjunction -/
example : (Adjunction.id : 𝟭 C ⊣ 𝟭 C).counit = 𝟙 (𝟭 C) := rfl

end IdentityAdjunction

end -- noncomputable

end CategoryTheoryTest.AdjunctionBasic

/-!
## Summary

Core functionality tested:
- Basic adjunction structure (3 definitions)
- Unit and counit access (2 definitions)
- Hom equivalence (2 definitions)
- Triangle identities (4 definitions)
- Naturality properties (4 definitions)
- Constructors (1 definition)
- Composition (1 definition)
- Typeclass instances (4 definitions)
- Identity adjunction (3 definitions)

Total: ~22 key definitions tested
-/