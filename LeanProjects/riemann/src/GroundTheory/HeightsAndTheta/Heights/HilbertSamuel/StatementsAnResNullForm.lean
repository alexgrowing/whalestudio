import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsBlockImage
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MeasureTheory

noncomputable section

def AnResNullForm.Statement : Prop :=
  ∀ (e : ℕ) (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P J : Ideal (MRing ι))
    (R : AnRes P J e) (G : MRing ι) (dG : K → ℕ),
    IsArithVar P (e + 1) → IsMultiHomog G dG → G ∉ P →
      ∀ j, volume ((R.A.chart j).target ∩
        (R.A.chart j).symm ⁻¹' {a | eval (R.lift a a) (map (Int.castRingHom ℂ) G) = 0}) = 0

section Inhabitants

open ProjLine

end Inhabitants

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
