import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.TwoBlockCycle
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

set_option linter.unusedSectionVars false

section Module

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

def modPieceCard (J₁ J₂ : Ideal (MRing ι)) (a : K → ℕ) : ℕ :=
  (J₂.restrictScalars ℤ ⊓ mHom ι a).toAddSubgroup.relIndex (J₁.restrictScalars ℤ ⊓ mHom ι a).toAddSubgroup

def topComps (J : Ideal (MRing ι)) (d : ℕ) : Set (Ideal (MRing ι)) :=
  {W | W ∈ J.minimalPrimes ∧ IsRelevant W ∧
    ringKrullDim (MRing ι ⧸ W) = ((d + Fintype.card K : ℕ) : WithBot ℕ∞)}

theorem modPieceCard_self (J : Ideal (MRing ι)) (a : K → ℕ) : modPieceCard J J a = 1 :=
  AddSubgroup.relIndex_self _

end Module

section TwoBlock

variable {Ω : Type} [Field Ω] [CharZero Ω] {κ : Type} [Fintype κ]

def twoBlockMOuter (x x' : Ix κ → Ω) (c : κ) : Ideal (MRing (FinTwoTypeFamily κ)) :=
  twoBlockIdeal x x' ⊔ Ideal.span (Set.range fun j : κ => twoBlockDen c * X ⟨1, j⟩)

def twoBlockMInner (x x' : Ix κ → Ω) (l : Ix κ → ℤ) : Ideal (MRing (FinTwoTypeFamily κ)) :=
  twoBlockIdeal x x' ⊔ Ideal.span (Set.range fun i : κ => twoBlockNum l * X ⟨0, i⟩)

end TwoBlock

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
