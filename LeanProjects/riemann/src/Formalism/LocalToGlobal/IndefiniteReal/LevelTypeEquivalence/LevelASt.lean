import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.BaseSt

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta NumberField

namespace Formalism.IndefR.Eqv

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable (D : D7)

def LevOKBase : Prop :=
  ∀ (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (N : ℕ)
    (L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank), Lev.IsBaseFrame V β Λ N →
    IsLevelA V (Formalism.L2.DIV.lev D.sp.cm V.gram β L) ∧
    ∃ U : Subgroup (GA D V), IsOpen (U : Set (GA D V)) ∧
      ∀ k ∈ U, k ∈ GfC V → k ∈ Lev.levG V β L ∧ Lev.levChi V β L k = 1

end Formalism.IndefR.Eqv

end
