import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ThetaKeyFormula.ZeroSetFinite
import GroundTheory.HeightsAndTheta.Heights.ThetaKeyFormula.RigSymFormTauIIsBasisOf
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.KeyFormula

open Complex Matrix

noncomputable section

open RigSymForm

def VanishingCechMultInvariants.Statement : Prop :=
  ∀ (P : RigSymForm ℂ) (a : ℕ), 3 ≤ a → ∀ (r : ℕ) (x : Fin (r + 1) → P.Fn), P.IsBasisOf a x →
    ∀ m : ℕ, 1 ≤ m → ∀ n q : ℕ,
      (∀ φ : Finset (Fin (r + 1)) → P.Fn,
        P.IsCocycle (a * m ^ 2) (n * m ^ 2) (q + 1) (fun j z => x j ((m : ℂ) • z)) φ →
        P.IsCoboundary (a * m ^ 2) (n * m ^ 2) q (fun j z => x j ((m : ℂ) • z)) φ) →
      ∀ φ : Finset (Fin (r + 1)) → P.Fn, P.IsCocycle a n (q + 1) x φ → P.IsCoboundary a n q x φ

end

end GroundTheory.Heights₂.Heights.KeyFormula
