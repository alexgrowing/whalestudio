import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.InfInvA
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.IILeft
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.DetOneAddSmulSingleSame
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.FderivXZxSkew

noncomputable section

open MeasureTheory Matrix
open scoped ContDiff

namespace PositivityTheory.Rg.Sw.LVs.II

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem eA_comm {n : ℕ} (a b : Fin n) : eA a b * JJ n = JJ n * eA a b := by
  simp [eA, JJ, Matrix.fromBlocks_multiply]

theorem eB_comm {n : ℕ} (a b : Fin n) : eB a b * JJ n = JJ n * eB a b := by
  simp [eB, JJ, Matrix.fromBlocks_multiply]

theorem infInv_of (hL : LeftDeriv) (hP : LawDeriv) (hI : PtId) (hC : CDiff) : InfInv := by
  intro n F1 F2 Ω hΩ hGΩ hF1 hF2 hlaw Kg _ _ _ _ _ _ μ _ ι hι hK Z
  have hΘc : ContDiffOn ℂ ∞ (fun y => F1 y * F2 y) Ω := hF1.mul hF2
  have hKk : ∀ k : Kg, InK (ι k) := fun k => (hK (ι k)).2 ⟨k, rfl⟩
  have hmem : ∀ k : Kg, ι k ∈ Ω := fun k => hGΩ (hKk k).1
  have hlawΘ := hP n (fun y => F1 y * F2 y) Ω hΩ hGΩ (hΘc.differentiableOn (by simp))
    (fun p x hp hp0 hx => hlaw p x hp hp0 hx)
  have hU : KSet n ⊆ Ω := fun g hg => hGΩ hg.1
  have hcd : ∀ c : M2 n → ℂ, ContDiff ℝ ∞ c →
      ContDiffOn ℝ 1 (fun y => c y * (F1 y * F2 y)) Ω := fun c hc =>
    (hc.contDiffOn.mul (hΘc.restrict_scalars ℝ)).of_le (by simp)
  have hA : ∀ a b : Fin n, Integrable (fun k => dK (fun y => cA Z a b y * (F1 y * F2 y)) (ι k) (eA a b)) μ ∧
      ∫ k, dK (fun y => cA Z a b y * (F1 y * F2 y)) (ι k) (eA a b) ∂μ = 0 := fun a b =>
    hL n Kg μ ι hι hK _ Ω hΩ hU (hcd _ (hC n Z a b).1) (eA a b) (eA_comm a b)
  have hB : ∀ a b : Fin n, Integrable (fun k => dK (fun y => cB Z a b y * (F1 y * F2 y)) (ι k) (eB a b)) μ ∧
      ∫ k, dK (fun y => cB Z a b y * (F1 y * F2 y)) (ι k) (eB a b) ∂μ = 0 := fun a b =>
    hL n Kg μ ι hι hK _ Ω hΩ hU (hcd _ (hC n Z a b).2) (eB a b) (eB_comm a b)
  have key : ∀ k : Kg, fderiv ℂ F1 (ι k) (ι k * Z) * F2 (ι k) + F1 (ι k) * fderiv ℂ F2 (ι k) (ι k * Z) =
      ∑ a : Fin n, ∑ b : Fin n, (dK (fun y => cA Z a b y * (F1 y * F2 y)) (ι k) (eA a b) +
        dK (fun y => cB Z a b y * (F1 y * F2 y)) (ι k) (eB a b)) := by
    intro k
    have hnh : Ω ∈ nhds (ι k) := hΩ.mem_nhds (hmem k)
    have hd1 : DifferentiableAt ℂ F1 (ι k) :=
      ((hF1.differentiableOn (by simp)) _ (hmem k)).differentiableAt hnh
    have hd2 : DifferentiableAt ℂ F2 (ι k) :=
      ((hF2.differentiableOn (by simp)) _ (hmem k)).differentiableAt hnh
    have hprod : fderiv ℂ (fun y => F1 y * F2 y) (ι k) (ι k * Z) =
        fderiv ℂ F1 (ι k) (ι k * Z) * F2 (ι k) + F1 (ι k) * fderiv ℂ F2 (ι k) (ι k * Z) := by
      have h : HasFDerivAt (fun y => F1 y * F2 y)
          (F1 (ι k) • fderiv ℂ F2 (ι k) + F2 (ι k) • fderiv ℂ F1 (ι k)) (ι k) :=
        hd1.hasFDerivAt.mul hd2.hasFDerivAt
      rw [h.fderiv]
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
      ring
    rw [← hprod]
    exact hI n (fun y => F1 y * F2 y) (ι k) Z (hKk k) ((hΘc.contDiffAt hnh).of_le (by simp))
      (fun Y hY => hlawΘ (ι k) (hKk k).1 Y hY)
  simp_rw [key]
  rw [integral_finset_sum]
  · refine Finset.sum_eq_zero (fun a _ => ?_)
    rw [integral_finset_sum]
    · refine Finset.sum_eq_zero (fun b _ => ?_)
      rw [integral_add (hA a b).1 (hB a b).1, (hA a b).2, (hB a b).2, add_zero]
    · intro b _
      exact (hA a b).1.add (hB a b).1
  · intro a _
    exact integrable_finset_sum _ (fun b _ => (hA a b).1.add (hB a b).1)

end PositivityTheory.Rg.Sw.LVs.II

namespace PositivityTheory.Rg.Sw.LVs

theorem infInv : InfInv := II.infInv_of II.leftDeriv II.lawDeriv II.ptId II.cDiff

end PositivityTheory.Rg.Sw.LVs
