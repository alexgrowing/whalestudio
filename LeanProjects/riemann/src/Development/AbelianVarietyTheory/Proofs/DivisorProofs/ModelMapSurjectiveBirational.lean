import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsCompModel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TopologicalKrullDimEqSucc
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCommonRefinementModels
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InducedMetricPullback
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ArTopOfInduced
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NefFibPullback
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Definitions.Divisors.EqOfSpecializesOfFinite
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalDegreePullbackFinite

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
open MvPolynomial Formalism.DegreeFormula Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.FlagPoly GlobalTheory.FlagAr
open CategoryTheory AlgebraicGeometry GlobalTheory GlobalTheory.TrueGeo GlobalTheory.ArInt ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.ProjVar

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ModelBirational

variable {F : Type} [Field F] [NumberField F] {Y : Var F}

theorem isPreimmersion_j (M : TrueGeo.Model Y) : IsPreimmersion M.j :=
  have h : IsPreimmersion (spMap (algebraMap (𝓞 F) F)) := IsPreimmersion.of_isLocalization (nonZeroDivisors (𝓞 F))
  MorphismProperty.of_isPullback (P := @IsPreimmersion) M.pb.flip h

theorem flat_j (M : TrueGeo.Model Y) : Flat M.j := by
  have : Flat (spMap (algebraMap (𝓞 F) F)) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    exact RingHom.flat_algebraMap_iff.2 (IsLocalization.flat F (nonZeroDivisors (𝓞 F)))
  exact MorphismProperty.of_isPullback (P := @Flat) M.pb.flip this

theorem j_genericPoint (M : TrueGeo.Model Y) :
    haveI := M.ar.isIntegral; M.j (genericPoint Y.X) = genericPoint M.X :=
  haveI := M.ar.isIntegral
  haveI := flat_j M
  RatFibreDeg.apply_genericPoint_of_flat M.j

theorem main : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (P M : TrueGeo.Model Y) (π : P.X ⟶ M.X), π ≫ M.p = P.p → P.j ≫ π = M.j → Surjective π ∧ (haveI := P.ar.isIntegral; π.residueDegree (genericPoint P.X) = 1) := by
  intro F _ _ Y P M π hp hj
  haveI := P.ar.isIntegral
  haveI := M.ar.isIntegral
  haveI := isPreimmersion_j P
  haveI := isPreimmersion_j M
  haveI : IsProper π := Mean4O.isProper_of_comp M.ar P.ar π hp
  have hg : π (genericPoint P.X) = genericPoint M.X := by
    rw [← j_genericPoint P, ← j_genericPoint M, ← hj, Scheme.Hom.comp_apply]
  refine ⟨⟨fun x => ?_⟩, ?_⟩
  · have h : closure {genericPoint M.X} ⊆ Set.range π :=
      closure_minimal (Set.singleton_subset_iff.2 ⟨_, hg⟩) π.isClosedMap.isClosed_range
    rw [genericPoint_closure] at h
    exact h trivial
  · have h₁ := CurveDegreesCompare.residueDegree_comp P.j π (genericPoint Y.X)
    rw [hj, j_genericPoint P] at h₁
    simpa only [RatFibreDeg.residueDegree_of_surjectiveOnStalks, mul_one, one_mul] using h₁.symm

end GlobalTheory.ModelBirational
