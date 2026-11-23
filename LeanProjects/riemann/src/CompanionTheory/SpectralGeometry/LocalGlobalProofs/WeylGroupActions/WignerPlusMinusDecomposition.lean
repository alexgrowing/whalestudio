import Mathlib
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ShiftAtRExistsEq
import Formalism.HermitianCurvature.FrameExists2
import Development.AbelianVarietyTheory.Definitions.Jets.WigMap
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.FormSubRight

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.CutBP2 Formalism.FourierDecayAlt.P.CutBPEq Matrix

namespace GlobalTheory.CompanionTheory.WigLowerOmg

theorem wigLower_omg : ∀ (Wq : Type) [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (Wqp : Type) [NormedAddCommGroup Wqp] [InnerProductSpace ℂ Wqp] [FiniteDimensional ℂ Wqp] (Wqm : Type) [NormedAddCommGroup Wqm] [InnerProductSpace ℂ Wqm] [FiniteDimensional ℂ Wqm] (k r : ℕ) (z z' : (Fin (2 * r + k + 1) → ℂ)) (b : ℝ) (n₀ : ℕ) (Ap : (Fin (2 * r + k + 1) → ℂ) → (Wqp →L[ℂ] Wq)) (Am : (Fin (2 * r + k + 1) → ℂ) → (Wqm →L[ℂ] Wq)), inWb k r z → 0 < Tz k r z → inWb k r z' → 0 < Tz k r z' → (∀ ω, inWb k r ω → herm (Hpk k r) ω z' = 0 → ∀ v : Wq, (herm (Hpk k r) ω ω).re ^ n₀ * ‖v‖ ^ 2 ≤ (3 * b) ^ (2 * n₀) * (‖ContinuousLinearMap.adjoint (Ap ω) v‖ ^ 2 + ‖ContinuousLinearMap.adjoint (Am ω) v‖ ^ 2)) → WigLower z z' b n₀ (fun g : B.Mat k r => Ap (GlobalTheory.WigSh.omg k r z z' (g))) (fun g : B.Mat k r => Am (GlobalTheory.WigSh.omg k r z z' (g))) := by
  intro Wq _ _ _ Wqp _ _ _ Wqm _ _ _ k r z z' b n₀ Ap Am hz hTz hz' hTz' hbound
  unfold WigLower
  intro g hg hGf v
  obtain ⟨hW, hperp, hre⟩ := GlobalTheory.WigSh.OmgNorm.omg_norm k r z z' g hz hTz hz' hTz' hg
  have h := hbound _ hW hperp v
  rw [hre] at h
  have hq : 0 < Gf k r z z' g / Tz k r z' := div_pos hGf hTz'
  have hqn := pow_pos hq n₀
  have key : ‖v‖ ^ 2 ≤ (3 * b) ^ (2 * n₀) *
      (‖ContinuousLinearMap.adjoint (Ap (GlobalTheory.WigSh.omg k r z z' g)) v‖ ^ 2 +
        ‖ContinuousLinearMap.adjoint (Am (GlobalTheory.WigSh.omg k r z z' g)) v‖ ^ 2) /
      (Gf k r z z' g / Tz k r z') ^ n₀ := by
    rw [le_div_iff₀ hqn, mul_comm]
    exact h
  refine key.trans (le_of_eq ?_)
  beta_reduce
  rw [← inv_div (Gf k r z z' g) (Tz k r z'), inv_pow]
  ring

end GlobalTheory.CompanionTheory.WigLowerOmg
