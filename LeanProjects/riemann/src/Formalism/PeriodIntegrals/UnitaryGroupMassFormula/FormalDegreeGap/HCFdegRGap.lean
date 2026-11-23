import Formalism.SharpRestriction.GlobalSchurBounds.TheoremThreeUnderScaleOfGeneral

noncomputable section

namespace PI.UnitaryGroupMassFormula.HCFdegRGap

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S

def HCFdegRGap : Prop :=
  ∀ (cd : CDHaar) (s : (n : ℕ) → (Fin n → Bool) → NNReal), Formalism.MainNotions.RT.cdScaleTieR cd s →
  ∀ (N : ℕ) (ε : Fin N → Bool) (lam : Fin N → ℝ) (h : ℝ),
    1 ≤ (Finset.univ.filter (fun a => ε a = true)).card →
    1 ≤ (Finset.univ.filter (fun a => ε a = false)).card →
    Formalism.QuantumDeterminants.IsHCParam lam → Formalism.QuantumDeterminants.GapAtLeast ε lam h →
    32 * (N : ℝ) * ((Finset.univ.filter (fun a => ε a = true)).card : ℝ) *
      ((Finset.univ.filter (fun a => ε a = false)).card : ℝ) + 2 < h →
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
      (σ : Matrix (Fin N) (Fin N) ℂ → (H →L[ℂ] H)) (w : H), IsDS ε lam σ → w ≠ 0 →
      fdegOf ((s N ε : ENNReal) • Formalism.REAL.muG ε) σ w = Formalism.QuantumDeterminants.fdegHC lam

end PI.UnitaryGroupMassFormula.HCFdegRGap
