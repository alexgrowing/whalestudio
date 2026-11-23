import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.XiPluckerRel
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI

noncomputable section

def PluckerCover.Statement : Prop :=
  ∀ (D : ℕ) (S : ProjectiveLineBundle D) (N : ℕ) (F : S.ι → S.ν → S.κ → S.κ → MRing S.YIdx), S.IsPluckerRel N F →
    ∃ (q : ℕ) (r : Fin q → MRing S.YIdx) (b : Fin q → T.YBlk → ℕ),
      (∀ j, IsMultiHomog (r j) (b j)) ∧ (∀ j, b j .line = 0) ∧
      (∀ j, rename (T.yyEmb 0) (r j) ∈ S.WW) ∧
      ∀ w : (Σ k, S.YIdx k) → ℂ, (∀ k, ∃ i, w ⟨k, i⟩ ≠ 0) →
        (∀ j, eval w (map (Int.castRingHom ℂ) (r j)) = 0) →
          ∃ i l k m, eval w (map (Int.castRingHom ℂ) (F i l k m)) ≠ 0

end

end GroundTheory.Heights₂.Heights.Inter
