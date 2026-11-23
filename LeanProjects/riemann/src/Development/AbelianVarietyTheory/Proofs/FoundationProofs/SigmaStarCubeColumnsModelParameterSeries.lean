import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.TheoremOfCubeOfAdditionFormulas
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OddThetaFunctionExistenceUniqueness
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DifferentiableSqTh
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TaylorSeriesInParameterRescaleOfAlgebraic
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SigmaStarSquareQuotientInModelParameter
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ColA
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.WeierstrassPFormalGroupLogUniformises
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators
open PowerSeries

noncomputable section

namespace GlobalTheory.FrobStick

theorem sgStar_atU {p : ℕ} [Fact p.Prime] (g : GL3Theta.G1 p) (hL : IsLat g.abelian₂) (hσ : AlgEnt (sgStar g.abelian₂)) :
    g.atU (sgStar g.abelian₂) =
      C ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) * X * ePhi1 g.lam g.abelian₂ g.C g.wq := by
  have h0 : coef1 (sgStar g.abelian₂) 0 = 0 := by
    simp [coef1, (hL.sg_eq_zero 0).2 (zero_mem _)]
  obtain ⟨S, hS⟩ : ∃ S : PowerSeries Qbar,
      PowerSeries.mk (coef1 (sgStar g.abelian₂)) = PowerSeries.map (algebraMap Qbar ℂ) (X * S) := by
    refine ⟨PowerSeries.mk fun n => ⟨coef1 (sgStar g.abelian₂) (n + 1), hσ.2 _⟩, ?_⟩
    ext n
    cases n with
    | zero => simp [h0]
    | succ n => rw [coeff_map, coeff_succ_X_mul, coeff_mk, coeff_mk]; rfl
  have hS' : GL3Theta.ser1 g.lam (sgStar g.abelian₂) = X * PowerSeries.map g.lam S := by
    rw [GlobalTheory.EvenTheta.Param.theta_series_map_coefficients g.lam _ _ hS, map_mul, map_X]
  have hE := GlobalTheory.EvenTheta.Param.X_mul_ePhi1 g _ hS'
  have hs := HasSubst.of_constantCoeff_zero'
    (GlobalTheory.SerTransport.const_Cl g ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]))
  rw [GlobalTheory.SerTransport.atU_eq, hS', subst_mul hs, subst_X hs, mul_assoc, mul_assoc, hE]

theorem colAB_atU : ∀ (p : ℕ) [Fact p.Prime] (g : GL3Theta.G1 p), IsWq g.W g.wq → IsLat g.abelian₂ → g2 g.abelian₂ ∈ Qbar → g3 g.abelian₂ ∈ Qbar → AlgEnt (sgStar g.abelian₂) → ∀ v, v ∉ g.abelian₂ → wpF g.abelian₂ v ∈ Qbar → AlgEnt (GlobalTheory.FrobStick.colA g.abelian₂) ∧ AlgEnt (GlobalTheory.FrobStick.colB g.abelian₂ v) ∧ g.atU (sgStar g.abelian₂) = PowerSeries.C ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) * PowerSeries.X * ePhi1 g.lam g.abelian₂ g.C g.wq ∧ g.atU (GlobalTheory.FrobStick.colA g.abelian₂) = PowerSeries.C (((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) ^ 3) * PowerSeries.X ^ 3 * ePhi1 g.lam g.abelian₂ g.C g.wq ^ 3 ∧ g.atU (GlobalTheory.FrobStick.colB g.abelian₂ v) = PowerSeries.C ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) * ePhi1 g.lam g.abelian₂ g.C g.wq ^ 3 * (PowerSeries.X * g.wq⁻¹ + PowerSeries.C (((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) ^ 2 * g.C.r) * PowerSeries.X ^ 3) := by
  intro p _ g hq hL h2 h3 hσ v hv hw
  obtain ⟨hT, hC, -, -⟩ := GlobalTheory.SerTransport.transport p g
  obtain ⟨aT, eT⟩ := GlobalTheory.EvenTheta.Param.sqTh_atU p g hq hL h2 h3 hσ v hv hw
  have e1 := sgStar_atU g hL hσ
  obtain ⟨⟨a2, e2⟩, -⟩ := hT _ _ hσ hσ
  obtain ⟨⟨a3, e3⟩, -⟩ := hT _ _ a2 hσ
  obtain ⟨aw, ew⟩ := hC _ hw
  obtain ⟨⟨a4, e4⟩, -⟩ := hT _ _ aw a2
  obtain ⟨-, a5, e5⟩ := hT _ _ aT a4
  obtain ⟨⟨a6, e6⟩, -⟩ := hT _ _ hσ a5
  have hA : colA g.abelian₂ = fun z => sgStar g.abelian₂ z * sgStar g.abelian₂ z * sgStar g.abelian₂ z := by
    funext z; rw [colA]; ring
  have hB : colB g.abelian₂ v = fun z => sgStar g.abelian₂ z *
      (sqTh g.abelian₂ v z + wpF g.abelian₂ v * (sgStar g.abelian₂ z * sgStar g.abelian₂ z)) := by
    funext z; rw [colB]; ring
  rw [hA, hB]
  refine ⟨a3, a6, e1, ?_, ?_⟩
  · rw [e3, e2, e1, map_pow]; ring
  · rw [e6, e5, e4, e2, ew, eT, e1, lineSer, xAt]
    simp only [map_mul, map_pow, map_sub]
    ring

end GlobalTheory.FrobStick
