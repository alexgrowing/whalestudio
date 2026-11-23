import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsArith
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsBergman
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.AnForm.M

noncomputable section

def ResolutionPullback.Statement : Prop :=
  ∀ (D : ℕ) (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    [CharZero Ω] (d : HSMBlockDatum D K ι Ω),
    ∃ (A : FinHolAtlas D d.R.X) (L : HolLineBundle A) (W : Weight L) (dV : SmoothVolume A),
      A.Compatible d.R.A ∧ W.IsSemipositive ∧ dV.μ = d.dV ∧
      ∀ (n : ℕ) (f : MRing ι), IsMultiHomog f (blockDeg d.k₀ n) →
        ∃ s ∈ L.sections n, ∀ x : d.R.X,
          ptNormSq W n s x =
            (‖eval (blockPt d x) (map (Int.castRingHom ℂ) f)‖ / d.A.h (blockPt d x) ^ n) ^ 2

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
