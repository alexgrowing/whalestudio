import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.UnipRat

noncomputable section

open Matrix NumberField Formalism.BasicNotions Formalism.L2.SG.HidaSetting

namespace Formalism.L2.SG.Pf.UnipB

open Formalism.L2.SG.Pf.Unip

def LatStepP {D : D7} (X : HidaSetting D) : Prop :=
  ∀ tY : ℕ, 0 < tY → ∃ ρ : ℝ, 0 ≤ ρ ∧ ∀ (k : ℕ), 1 ≤ k → ∀ (P : InfinitePlace X.B.I.F → Matrix (Kap X) (Kap X) ℂ),
    (∀ v, InPat (lvk X) k (P v)) → (∀ v, (P v)ᴴ * JBv X v = -(JBv X v * P v)) →
    ∃ Y : Matrix (Kap X) (Kap X) X.B.I.E, InPat (lvk X) k Y ∧ Yᴴ * JB X = -(JB X * Y) ∧ IntDiv tY Y ∧
      ∀ v i j, ‖(P v - Y.map (X.B.I.φ v)) i j‖ ≤ ρ

def LatStepC : Prop := ∀ (D : D7) (X : HidaSetting D), LatStepP X

end Formalism.L2.SG.Pf.UnipB
