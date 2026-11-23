import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPrAlt
import Formalism.HermitianCurvature.StatementTBB
import Formalism.SharpRestriction.CuspSpanNormBounds.LeadMinorK

noncomputable section

namespace BpJoin

open Formalism.FourierDecayAlt

def ThmBpDS : Prop :=
  ∀ Ch C₀ : ℝ, 0 ≤ C₀ → ∃ C₄ Cg₀ : ℝ, 0 ≤ C₄ ∧ ∀ Cg : ℝ, Cg₀ ≤ Cg →
    ∀ (P : M.Par) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
      [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (p : KB.Pl P Wp Wq)
      (lam lam' : Fin (2 * P.r + P.k + 1) → ℝ) (ka b : ℝ) (n₀ p₀ : ℕ) (R : BranchingSupport.Rep P.k P.r)
      (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)),
      Formalism.MainNotions.S.ThB.StdHyp Ch Cg P.k P.r (PI.BesselPeriodGGP.eps48 P.k P.r) lam
        (fun i => P.u (i.val + 1)) (fun i => P.u' (i.val + 1))
        (P.T * (1 / ka) ^ (2 * P.r)) (P.T' * (1 / ka) ^ (2 * P.r)) ka b →
      Formalism.MainNotions.S.ThB.AllGaps lam (200 * Formalism.MainNotions.S.ThB.l1 lam' lam) →
      R.IsDS (PI.BesselPeriodGGP.eps48 P.k P.r) lam' →
      (haveI := FiniteDimensional.complete ℂ Wp; PI.CapelliEig.IsKFinCoefT (k := P.k) (r := P.r) R.σ f) →
      ((∀ i ∈ Finset.Icc 1 P.k, P.u i = P.u' i) → n₀ = 30 * (P.r + 1) ^ 2 + 6) →
      (¬ (∀ i ∈ Finset.Icc 1 P.k, P.u i = P.u' i) → n₀ = 0) →
      3 * (P.r + 1) ≤ 2 * p₀ → (p₀ : ℝ) ≤ C₀ * ((P.r : ℝ) + 1) ^ 2 →
      TBB.ThmBpAt p f b C₄ n₀ p₀

end BpJoin
