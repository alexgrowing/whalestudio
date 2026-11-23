import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsCoreLat
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.EisRegularAtOfEisPoleLE
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqExistsIffDsExists
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaInnerProductHermitian
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemLatOIffExistsActO
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped ComplexConjugate TensorProduct
open Matrix

noncomputable section

namespace GlobalTheory.TargetCoef

theorem coef_zero_of_target_eigen : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om →
    ∀ (m : Measure (WO S T)) (X : Set (WO S T)), IsCovolOne (ratL T S) m X → ∀ F : WO S T → ℂ, IsThetaFunO ψ S T F →
    ∀ (g : GA D T) (y : WO S T) (a b : AF D.host.F), heisO ψ S T y F = ψ a • F →
    heisO ψ S T (actO S T 1 g⁻¹ y) F = ψ b • F → ψ a ≠ ψ b → ∫ w in X, om (1, g) F w * conj (F w) ∂m = 0 := by
  intro D ψ S T χS χT om hw m X hm F hF g y a b ha hb hab
  have hψ := hw.std
  have hG : IsThetaFunO ψ S T (om (1, g) F) := hw.om_pres _ F hF
  have hact : actO S T 1 g (actO S T 1 g⁻¹ y) = y := by
    have := GlobalTheory.AdelicLatMove.actO_actO_inv S T 1 g y
    rwa [inv_one] at this
  have hy : heisO ψ S T y (om (1, g) F) = ψ b • om (1, g) F := by
    have e := hw.om_heis 1 g (actO S T 1 g⁻¹ y) F hF
    rw [hb, map_smul, hact] at e
    exact e.symm
  have hU := ((GlobalTheory.ThetaPairingLaws.ipO_laws D ψ S T m X hψ hm _ _ hG hF).2.2.2.2.2.2.1 y).1
  rw [hy, ha] at hU
  unfold GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.ipO at hU
  have hI : (∫ w in X, (ψ b • om (1, g) F) w * conj ((ψ a • F) w) ∂m) =
      (ψ b * conj (ψ a)) * ∫ w in X, om (1, g) F w * conj (F w) ∂m := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
    simp only [Pi.smul_apply, smul_eq_mul, map_mul]
    ring
  rw [hI] at hU
  have hn : conj (ψ a) * ψ a = 1 := by
    rw [Complex.conj_mul', hψ.1.2.1 a]
    simp
  by_contra hne
  have hc : ψ b * conj (ψ a) = 1 := by
    have := congrArg (· / ∫ w in X, om (1, g) F w * conj (F w) ∂m) hU
    simpa [mul_div_assoc, div_self hne] using this
  apply hab
  calc ψ a = (ψ b * conj (ψ a)) * ψ a := by rw [hc, one_mul]
    _ = ψ b * (conj (ψ a) * ψ a) := by ring
    _ = ψ b := by rw [hn, mul_one]

end GlobalTheory.TargetCoef

end
