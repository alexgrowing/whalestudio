import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.TheoremOfCubeOfAdditionFormulas
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OddThetaFunctionExistenceUniqueness
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DifferentiableSqTh
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TaylorSeriesInParameterRescaleOfAlgebraic
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SigmaStarSquareQuotientInModelParameter
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ColA
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IdealPeriodLatticeOfCurveDatum
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralJAndAlgebraicData
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InducedTypeThetaGenusOnePermutes
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmThetaTaylorCoeffAlgebraicAndConjugate
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators
open PowerSeries

namespace GlobalTheory.FrobStick.AtData

theorem weierstrass_translate_zero_eq_self (Λ : AddSubgroup ℂ) (F : ℂ → ℂ) : U1 Λ 0 F = F := by
  funext z; simp [U1]

theorem half_gen {Λ : AddSubgroup ℂ} (hlat : IsLat Λ) : ∃ v : ℂ, v ∉ Λ ∧ InRationalLattice Λ v := by
  obtain ⟨w₁, w₂, hli, rfl⟩ := hlat
  refine ⟨w₁ / 2, ?_, ⟨2, by norm_num, ?_⟩⟩
  · intro h
    rw [AddSubgroup.mem_closure_pair] at h
    obtain ⟨m, n, hmn⟩ := h
    have key := (LinearIndependent.pair_iff.1 hli) ((m : ℝ) - 1 / 2) (n : ℝ) (by
      have e : (m : ℂ) * w₁ + (n : ℂ) * w₂ = w₁ / 2 := by simpa [zsmul_eq_mul] using hmn
      simp only [Complex.real_smul]
      push_cast
      linear_combination e)
    have h1 : (m : ℝ) = 1 / 2 := by linarith [key.1]
    have h2 : (2 * m : ℝ) = 1 := by linarith
    have h3 : (2 * m : ℤ) = 1 := by exact_mod_cast h2
    omega
  · have : (2 : ℂ) * (w₁ / 2) = w₁ := by ring
    push_cast
    rw [this]
    exact AddSubgroup.subset_closure (by simp)

theorem atData : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (g : GL3Theta.G1 p), GL3Theta.At D cc δ g → IsWq g.W g.wq ∧ IsLat g.abelian₂ ∧ g2 g.abelian₂ ∈ Qbar ∧ g3 g.abelian₂ ∈ Qbar ∧ AlgEnt (sgStar g.abelian₂) ∧ ∃ v : ℂ, v ∉ g.abelian₂ ∧ wpF g.abelian₂ v ∈ Qbar := by
  intro D p _ cc δ g hg
  obtain ⟨hcc, -, hδ, hΛ, hok⟩ := hg
  have hcrv : Crv D cc δ := ⟨hcc, hδ⟩
  have hG := (GlobalTheory.InducedType.induced_type D).1
  obtain ⟨hlat, -⟩ := GlobalTheory.CurveLattice.lattice_of_curve D hG cc δ hcrv
  obtain ⟨⟨-, h2, h3⟩, hwp⟩ := (GlobalTheory.CurveAlgebraic.integral_j_and_algebraic_data D hG).2 cc δ hcrv
  have huse := (GlobalTheory.ThetaConj.cmTheta_taylorCoeff_algebraic_and_conjugate D cc δ hcrv).1
  simp only [tor0] at h2 h3
  rw [← hΛ] at hlat h2 h3 hwp huse
  have hlat' : IsLat g.abelian₂ := hlat
  obtain ⟨v, hv, hvq⟩ := half_gen hlat'
  refine ⟨hok.2.1, hlat', h2, h3, ⟨hlat'.differentiable, fun n => ?_⟩, v, hv, (hwp v hvq hv).1⟩
  have := huse 0 ⟨1, one_pos, by simp⟩ n
  rwa [weierstrass_translate_zero_eq_self] at this

end GlobalTheory.FrobStick.AtData
