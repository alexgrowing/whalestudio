import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QSPow
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FirstIndexEqOfUnfolded
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.FirstMinimumInvariantContinuousPosOnFrames

namespace GlobalTheory.ScalarPoin

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst MeasureTheory

theorem lintegral_kaF_lt_top : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r)
    (x0 : Frame X.Ψ r), IsOrth X x0 → ∃ s0 : ℝ, ∀ s : ℝ, s0 ≤ s →
      ∫⁻ z, ENNReal.ofReal (kaF X x0 s z) ∂muF X x0 < ⊤ := by
  intro E _ _ _ r X x0 ho
  obtain ⟨FF, hF⟩ := GlobalTheory.MetricWeightTest.exists_fundSet_orth X ho
  have hfin := (GlobalTheory.TrueCx.covol_eq X ho hF).1
  refine ⟨4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 + 1, fun s hs => ?_⟩
  obtain ⟨C, hC, hCb⟩ := kaUnfoldStatement_holds r X x0 ho (GlobalTheory.ClosedDiscontinuity.propDisc_closed r X) FF hF s
    (by linarith)
  have h := hCb (fun _ => 1) measurable_const (fun _ _ _ _ => rfl) (fun _ _ _ _ => rfl)
  simp only [mul_one, lintegral_const, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, one_mul] at h
  exact h.trans_lt (ENNReal.mul_lt_top hC hfin)

end GlobalTheory.ScalarPoin
