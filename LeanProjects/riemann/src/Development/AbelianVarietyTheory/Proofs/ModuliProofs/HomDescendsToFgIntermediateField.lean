import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AuxiliaryInertOddPrime
import Development.AbelianVarietyTheory.Statements.HeckeInFamilies.GenericMemChart
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MorphismsSpreadOutToFgSubalgebra

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

namespace GlobalTheory

theorem hom_descends_to_fg_intermediateField : ∀ (K C : Type) [Field K] [Field C] [Algebra K C] (A B : Over (Sp K)) (f : (Over.pullback (spMap (algebraMap K C))).obj A ⟶ (Over.pullback (spMap (algebraMap K C))).obj B), LocallyOfFiniteType A.hom → QuasiCompact A.hom → IsSeparated A.hom → LocallyOfFiniteType B.hom → ∃ (L : IntermediateField K C) (f₀ : pullback A.hom (spMap (algebraMap K L)) ⟶ B.left), L.FG ∧ f₀ ≫ B.hom = pullback.fst _ _ ≫ A.hom ∧ ∀ i : pullback A.hom (spMap (algebraMap K C)) ⟶ pullback A.hom (spMap (algebraMap K L)), i ≫ pullback.fst _ _ = pullback.fst _ _ → i ≫ pullback.snd _ _ = pullback.snd _ _ ≫ spMap (algebraMap L C) → i ≫ f₀ = f.left ≫ pullback.fst _ _ := by
  intro K C _ _ _ A B f _ _ _ _
  have hw : f.left ≫ pullback.snd B.hom (spMap (algebraMap K C)) =
      pullback.snd A.hom (spMap (algebraMap K C)) := by
    simpa using Over.w f
  have hφ : (f.left ≫ pullback.fst _ _) ≫ B.hom = pullback.fst _ _ ≫ A.hom := by
    rw [Category.assoc, pullback.condition, reassoc_of% hw, pullback.condition]
  obtain ⟨R, ψ, hR, hψ, hRψ⟩ := Spread.exists_fg_comp_eq A.hom B.hom (f.left ≫ pullback.fst _ _) hφ
  obtain ⟨t, rfl⟩ := hR
  let L : IntermediateField K C := IntermediateField.adjoin K (t : Set C)
  have hle : Algebra.adjoin K (t : Set C) ≤ L.toSubalgebra :=
    IntermediateField.algebra_adjoin_le_adjoin K _
  refine ⟨L, Spread.bcMap A.hom (Subalgebra.inclusion hle) ≫ ψ, ⟨t, rfl⟩, ?_, ?_⟩
  · rw [Category.assoc, hψ, Spread.bcMap_fst_assoc]
  · intro i h₁ h₂
    rw [Spread.eq_bcMap A.hom L.val h₁ h₂, ← Category.assoc,
      Spread.bcMap_comp_of_eq A.hom _ _ (Algebra.adjoin K (t : Set C)).val fun _ ↦ rfl, hRψ]

end GlobalTheory
