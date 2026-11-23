import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.SnapperCutObj
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

def subsetDiff (n : ℕ) (f : (Fin (n + 1) → ℕ) → ℤ → ℚ) (m : ℕ) (c : ℤ) : ℚ :=
  ∑ T : Finset (Fin n), (-1 : ℚ) ^ (n - T.card) *
    f (Fin.snoc (α := fun _ => ℕ) (fun i => if i ∈ T then 1 else 0) m) c

def SubsetDiffConst.Statement : Prop :=
  ∀ (n : ℕ) (f : (Fin (n + 1) → ℕ) → ℤ → ℚ), IsNumPolyLT (n + 1) (n + 1) f →
    (∀ (m m' : ℕ) (c c' : ℤ), subsetDiff n f m c = subsetDiff n f m' c') ∧
      (IsNumPolyLT (n + 1) n f → ∀ (m : ℕ) (c : ℤ), subsetDiff n f m c = 0)

end

end GroundTheory.Heights₂.Heights.Kleiman
