import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsHSMTransport
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def ResChiIndex.Statement : Prop :=
  ∀ (D : ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (κ : Type) [Fintype κ] (d d' : HSMDatum D Ω κ)
    (B : Matrix (Ix κ) (Ix κ) ℚ), IsInvMat B → d'.x = matAct B d.x →
    (∀ (n r : ℕ) (b : Fin r → MvPolynomial (Ix κ) ℚ), resGram d' n b = resGram d n fun k => matSubst B (b k)) →
    ∀ n : ℕ, resChi d' n - resChi d n = latLogIndex d.x d'.x n

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
