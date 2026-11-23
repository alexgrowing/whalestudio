import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AnalyticLogResolution
import ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffAtOfIsPotential
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundaryPshExhaustionWeightsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartSumIntegralLeMongeAmpereStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PshPullbackHolomorphicStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasurableAbsLogNormSectionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MongeAmpereExhaustionLimitStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogResidueChernBoundProjectiveStatement
open MeasureTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.IndefiniteRowSideFullHecke.BoundaryPolynomialFunctions GlobalTheory.LogResInt
open scoped ENNReal

namespace GlobalTheory.LogResInt

theorem onResolution : ∀ (d : ℕ) (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (A : FinHolAtlas d X) (m : ℕ) (α : LocPot X) (Λ : Fin m → LocPot X) (σ : Fin m → X → X → ℂ) (c : ℝ),
    IsBoundarySetting A α Λ σ c →
    ∀ (L : LocPot X) (s : X → X → ℂ), IsPotential A L → IsSection A L s → (∀ y, normSec L s y ≤ 1) →
    ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [CompactSpace Y] [T2Space Y] (B : FinHolAtlas n Y),
    IsProjective B → ∀ (μ : Y → X) (hμ : HoloMap B A μ) (r : ℕ) (W : Fin r → Set Y)
    (e : Fin (m + 1) → Fin r → ℕ),
    IsJointSNC B μ (Fin.cons L Λ) (Fin.cons s σ) W e →
    (∀ k, 1 ≤ e 0 k → (∃ i : Fin m, 1 ≤ e i.succ k) → RankDropAlong A μ B (W k)) →
    chartSumInt B ((poincarePot α Λ σ c).pullback μ hμ.1) (μ ⁻¹' boundary σ)ᶜ
      (fun y => absLogNorm L s (μ y)) < ∞ := by
  intro d X _ _ _ A m α Λ σ c hset L s hL hs hs1 n Y _ _ _ B hproj μ hμ r W e hsnc hrank
  obtain ⟨w, K, O, hw, hpsh, hbd, hO, hmono, -, hcov, hloc⟩ := GlobalTheory.T.boundary_psh_exhaustion_weights d X A m α Λ σ c hset
  letI : MeasurableSpace Y := borel Y
  haveI : BorelSpace Y := ⟨rfl⟩
  obtain ⟨C, hC, hJ⟩ := GlobalTheory.T.log_residue_chern_bound_projective d X A m α Λ σ c hset L s hL hs hs1 n Y B hproj μ hμ r W e hsnc hrank
    w K hw hpsh hbd
  have hpotX : ∀ R, IsPotential A (α + LocPot.ofFun (w R)) := fun R =>
    isPotentialAdd A _ _ hset.1 (isPotential_ofFun A _ (hw R))
  refine GlobalTheory.T.monge_ampere_exhaustion_limit d X A n Y B μ hμ (poincarePot α Λ σ c) (fun R => α + LocPot.ofFun (w R)) O
    (fun _ => 0) _ _ ((B.n : ℝ≥0∞) * C) hpotX hO hmono ?_ ?_ ?_ ?_ ?_
  · intro R x y hy
    show α.φ x y + w R y = α.φ x y + pFun Λ σ c y / 2 + 0
    rw [hloc R y hy, add_zero]
  · intro y hy
    exact hcov (μ y) hy
  · intro _ _
    exact GlobalTheory.T.measurable_abs_log_norm_section d X A L s hL hs Y μ hμ.1
  · exact ENNReal.mul_lt_top (ENNReal.natCast_lt_top _) hC
  · intro R
    refine (GlobalTheory.T.chart_sum_integral_le_monge_ampere n Y B _ (isPotentialPullback A B μ hμ _ (hpotX R))
      (GlobalTheory.T.psh_pullback_holomorphic d X A n Y B μ hμ _ (hpotX R) (hpsh R)) _ _ (GlobalTheory.T.measurable_abs_log_norm_section d X A L s hL hs Y μ hμ.1)).trans ?_
    gcongr
    exact hJ R

end GlobalTheory.LogResInt
