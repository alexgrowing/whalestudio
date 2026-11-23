import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ProperRelAmpleKTrivOfFieldExtension

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.AmpleDescent

theorem relAmple_of_fieldExtension : ∀ (K₀ K : Type) [Field K₀] [Field K] (i : K₀ →+* K) (A₀ : Over (Sp K₀)) (A : Over (Sp K)) [GrpObj A₀] [GrpObj A] (φ : A.left ⟶ A₀.left) (L₀ : LB A₀.left) (L : LB A.left), IsAbelianScheme A₀ → IsGrpPullback A A₀ (spMap i) φ → L₀.IsLB → L.IsLB → LBIso L (L₀.pull φ) → Out.RelAmple A L → Out.RelAmple A₀ L₀ := by
  intro K₀ K _ _ i A₀ A _ _ φ L₀ L hab hpb hL₀ hL hiso hA

  have : IsProper A₀.hom := hab.proper
  have hP : IsPullback φ A.hom A₀.hom (spMap i) := hpb.1
  have : IsProper A.hom := MorphismProperty.of_isPullback (P := @IsProper) hP this

  have h1 : IsAmpleLB (L₀.pull φ) :=
    (GlobalTheory.isAmpleLB_congr hL (pull_isLB hL₀ φ) hiso).1 ((GlobalTheory.relAmple_iff_isAmpleLB_of_isAffine A hL).1 hA)

  have : CompactSpace A₀.left := QuasiCompact.compactSpace_of_compactSpace A₀.hom
  have : QuasiSeparatedSpace A₀.left := quasiSeparatedSpace_of_quasiSeparated A₀.hom

  exact (GlobalTheory.relAmple_iff_isAmpleLB_of_isAffine A₀ hL₀).2 (GlobalTheory.AmpleDescent.isAmpleLB_of_pull i hP hL₀ h1)

end GlobalTheory.AmpleDescent
