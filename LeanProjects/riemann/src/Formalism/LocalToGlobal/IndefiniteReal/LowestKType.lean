import Formalism.LocalToGlobal.IndefiniteReal.PublishedAut
import Formalism.LocalToGlobal.IndefiniteReal.SmExpSmulContDiff
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.HarishChandraMultiplicityBound

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta

namespace Formalism.IndefR.LowestKTypeSmoothness

attribute [local instance] Formalism.BasicNotions.Host.cmStar

lemma smoothOnH_of_isSmoothVecU {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (ε : Fin n → Bool) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (w : H)
    (h : ReciprocityTheory.ChartRestriction.DS.IsSmoothVecU ε σ w) :
    PI.UpqRep.SmoothOnH (PI.UpqRep.Jm ε) (fun g => σ g w) :=
  h

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar}

def LowSmooth {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : Formalism.IndefR.Mult.DSModel V S) : Prop :=
  ∀ τ, ∀ w ∈ Formalism.MainNotions.S.lowKSub (M.ε τ) (M.lam τ) (M.σ τ), w ∈ M.sm τ

end Formalism.IndefR.LowestKTypeSmoothness

end
