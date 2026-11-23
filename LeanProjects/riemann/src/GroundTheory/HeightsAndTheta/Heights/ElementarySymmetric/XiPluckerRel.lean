import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsAntisym
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI

noncomputable section

namespace ProjectiveLineBundle

variable {D : ℕ} (S : ProjectiveLineBundle D)

def pluckerWW (k m : S.κ) : MRing S.WIdx :=
  X ⟨.line0, k⟩ * X ⟨.line1, m⟩ - X ⟨.line0, m⟩ * X ⟨.line1, k⟩

def IsPluckerRel (N : ℕ) (F : S.ι → S.ν → S.κ → S.κ → MRing S.YIdx) : Prop :=
  (∀ i l k m, IsMultiHomog (F i l k m) (Pi.single T.YBlk.base (N + 3))) ∧
    ∀ i l k m, S.g * rename (T.yyEmb 0) (F i l k m) -
      S.h * S.pluckerWW k m * X ⟨.det, l⟩ * X ⟨.base, i⟩ ^ N ∈ S.WW

end ProjectiveLineBundle

def PluckerRel.Statement : Prop :=
  ∀ (D : ℕ) (S : ProjectiveLineBundle D), ∃ (N : ℕ) (F : S.ι → S.ν → S.κ → S.κ → MRing S.YIdx), S.IsPluckerRel N F

section Inhabit

def exPluckerF : Unit → Unit → Unit ⊕ Unit → Unit ⊕ Unit → MRing ExY
  | _, _, .inl _, .inr _ => X ⟨.base, ()⟩ ^ 3
  | _, _, .inr _, .inl _ => -X ⟨.base, ()⟩ ^ 3
  | _, _, _, _ => 0

end Inhabit

end

end GroundTheory.Heights₂.Heights.Inter
