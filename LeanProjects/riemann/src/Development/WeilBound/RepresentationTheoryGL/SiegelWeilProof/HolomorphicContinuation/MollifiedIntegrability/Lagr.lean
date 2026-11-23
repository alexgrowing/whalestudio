import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.ClsGainBSt

noncomputable section

namespace PositivityTheory.Rg.Sw.WR.K.GB

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR

def Twist : Prop :=
  ∀ (n : ℕ) (H : E n → ℂ), ContDiff ℝ (⊤ : ℕ∞) H → ∀ N : ℕ, ∃ G : ℕ → E n → ℂ,
    (∀ j, ContDiff ℝ (⊤ : ℕ∞) (G j)) ∧ ∀ (z : ℂ) (y : E n),
      (Delta^[N] (fun y => ((dP y : ℝ) : ℂ) ^ (-z) * H y)) y =
        ((dP y : ℝ) : ℂ) ^ (-z) * ∑ j ∈ Finset.range (n * N + 1), z ^ j * G j y

def Lagr : Prop :=
  ∀ D : ℕ, ∃ C : ℝ, ∀ (c : ℕ → ℂ) (B : ℝ), (∀ i ≤ D, ‖∑ j ∈ Finset.range (D + 1), ((i : ℕ) : ℂ) ^ j * c j‖ ≤ B) →
    ∀ j ≤ D, ‖c j‖ ≤ C * B

end PositivityTheory.Rg.Sw.WR.K.GB
