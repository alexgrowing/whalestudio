import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ProjFrameGraphChart
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

noncomputable section

def ProjFrameFibreDeg.Statement : Prop :=
  ∀ (D : ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (κ : Type) [Fintype κ] (x : Ix κ → Ω) (e : Fin (D + 1) → Ix κ),
    IsArithVar (ι := GlobalTheory κ) (coordIdeal ℤ x) (D + 1) → IsProjFrame x e →
    ∀ (G : GenFibre (inrV (ι := GlobalTheory κ) (ι₂ := GlobalTheory (Fin (D + 1))))
        (graphIdeal (coordIdeal ℤ x) (linForm (ι := GlobalTheory κ) (ι₂ := GlobalTheory (Fin (D + 1))) (projMat e))))
      (i : (k : FibreBlock (Sum.inr : Unit → Unit ⊕ Unit)) → fibreIdx (Sum.elim (GlobalTheory κ) (GlobalTheory (Fin (D + 1)))) Sum.inr k),
      IsChart (ReciprocityTheory.ChartRestriction.G.AI.I4.fibreIdeal (Sum.inr : Unit → Unit ⊕ Unit) G) i →
      ptDeg (ReciprocityTheory.ChartRestriction.G.AI.I4.fibreIdeal (Sum.inr : Unit → Unit ⊕ Unit) G) i = projDeg x e

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
