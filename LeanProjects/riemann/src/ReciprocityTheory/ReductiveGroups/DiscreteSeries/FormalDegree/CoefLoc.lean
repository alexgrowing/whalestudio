import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.CoefWeightedG
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.CoefLocGap

noncomputable section

open MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS

def CoefWeightedLoc : Prop :=
  ∀ (k r : ℕ) (v : Fin (k - 1) → ℝ) (b : Fin (2 * r + 2) → ℝ),
    Formalism.QuantumDeterminants.IsHCParam (Formalism.MainNotions.CayleySignature.lam48 k r v b) → Formalism.MainNotions.CayleySignature.GapBig k r b →
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
      (σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)),
      Formalism.MainNotions.S.IsDS (Formalism.MainNotions.CayleySignature.eps48 k r) (Formalism.MainNotions.CayleySignature.lam48 k r v b) σ →
      ∀ w : H, Formalism.MainNotions.S.IsLowUnit (Formalism.MainNotions.CayleySignature.eps48 k r) (Formalism.MainNotions.CayleySignature.lam48 k r v b) σ w →
        ∫⁻ g, ‖⟪w, σ (Formalism.MainNotions.S.uMat g) w⟫_ℂ‖ₑ *
            ENNReal.ofReal (‖Matrix.toEuclideanCLM (𝕜 := ℂ) (Formalism.MainNotions.S.uMat g)‖ ^
              (4 * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 * Real.sqrt (2 * ((r + 1 : ℕ) : ℝ))))
          ∂(Formalism.REAL.muG (Formalism.MainNotions.CayleySignature.eps48 k r)) < ⊤

theorem coefWeightedLoc : CoefWeightedLoc := by
  intro k r v b hlam hgap H _ _ σ hDS w hw
  obtain ⟨h, hg, hthr⟩ := cayley_weight_gap k r v b hlam hgap
  exact coefWeightedN (Formalism.MainNotions.CayleySignature.eps48 k r) (Formalism.MainNotions.CayleySignature.lam48 k r v b) σ hlam hDS w hw h hg _
    (by positivity) hthr _

end ReciprocityTheory.ChartRestriction.DS
