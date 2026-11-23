import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.SmoothGaloisGeometry.ConnectedSpacePullbackOfIsIntegral
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.SmoothGaloisGeometry.IsStrictlySemistableCompOpenImmersion
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.SmoothGaloisGeometry.NormLtOneOfIrreducible
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace CrystallineSemistableComparison

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

theorem Model.good_sub (M : Model l K) (hM : M.Good) (U : M.X.Opens) (hU : IsClosed (U : Set M.X)) :
    (M.sub U).Good := by
  obtain ⟨⟨N, i, hi, hcomp⟩, ϖ, hϖ, hss⟩ := hM
  have : IsClosedImmersion U.ι := .of_isPreimmersion _ (by rw [Scheme.Opens.range_ι]; exact hU)
  refine ⟨⟨N, U.ι ≫ i, inferInstance, by rw [Category.assoc, hcomp]⟩, ϖ, hϖ, ?_⟩
  exact isStrictlySemistable_comp_openImmersion ϖ M.p hss U.ι

theorem Model.sm_sub (M : Model l K) (hM : M.Sm) (U : M.X.Opens) (hU : IsClosed (U : Set M.X)) :
    (M.sub U).Sm := by
  have := hM.2
  exact ⟨M.good_sub hM.1 U hU, inferInstanceAs (Smooth (U.ι ≫ M.p))⟩

theorem Model.noetherianSpace [FiniteDimensional ℚ_[l] K] (M : Model l K) (hM : M.Good) :
    NoetherianSpace M.X := by
  have := OK_dvr (l := l) (K := K)
  obtain ⟨⟨N, i, hi, hcomp⟩, -⟩ := hM
  have : IsProper (PSpace.str (OK l K) N) := isProper_str _ N
  have : IsLocallyNoetherian M.X := by
    exact LocallyOfFiniteType.isLocallyNoetherian (i ≫ PSpace.str (OK l K) N)
  have : CompactSpace M.X := by
    exact QuasiCompact.compactSpace_of_compactSpace (i ≫ PSpace.str (OK l K) N)
  have : IsNoetherian M.X := {}
  infer_instance

theorem isOpenImmersion_gen [FiniteDimensional ℚ_[l] K] :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom (OK l K).subtype)) := by
  have := OK_dvr (l := l) (K := K)
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (OK l K)
  have := OK_away hϖ
  exact IsOpenImmersion.of_isLocalization (S := K) ϖ

theorem compSm : ∀ (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)) [FiniteDimensional ℚ_[l] K],
    CompM (Model.Sm (l := l) (K := K)) := by
  intro l _ K _
  have := OK_dvr (l := l) (K := K)
  refine compM_of _ isOpenImmersion_gen (fun M hM U hU ↦ M.sm_sub hM U hU) (fun M hM ↦ M.noetherianSpace hM.1) ?_
  intro M hM
  have := hM.2
  have hS : GlobalTheory.IsNormalScheme (Spec (CommRingCat.of (OK l K))) := inferInstance
  refine ⟨GlobalTheory.isNormalScheme_of_smooth M.p, LocallyOfFiniteType.isLocallyNoetherian M.p,
    Flat.generalizingMap M.p, inferInstance⟩

end CrystallineSemistableComparison
