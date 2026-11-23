import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsArith
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo

def ZCombExpand.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ), IsIntersectionFamily I →
    ∀ (P : Ideal (MRing ι)) (d : ℕ) (M H : HermLine ι) (q p : ℕ),
      IsArithVar P d → IsSmoothHerm M → IsSmoothHerm H →
      I P d (fun _ => HermLine.zcomb M H (q : ℤ) (p : ℤ)) =
          ∑ i ∈ Finset.range (d + 1), (d.choose i : ℝ) * (q : ℝ) ^ (d - i) * (p : ℝ) ^ i *
            I P d (fun j : Fin d => if (j : ℕ) < d - i then M else H) ∧
        (1 ≤ d → I P d (fun j : Fin d => if (j : ℕ) = 0 then M else HermLine.zcomb M H (q : ℤ) (p : ℤ)) =
          ∑ i ∈ Finset.range d, ((d - 1).choose i : ℝ) * (q : ℝ) ^ (d - 1 - i) * (p : ℝ) ^ i *
            I P d (fun j : Fin d => if (j : ℕ) < d - i then M else H))

end GroundTheory.Heights₂.Heights.HilbertSamuel
