import Formalism.LocalToGlobal.GlobalTheory.WeightLevelZeroEqOne
import Formalism.LocalToGlobal.GlobalTheory.ColValOfTiedSOfRest

noncomputable section

open Matrix TensorProduct NumberField IsDedekindDomain

namespace Formalism.L2.GlobalTheoryTheory.ColValS

open Formalism.UG Formalism.UG.CS Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Herm Formalism.L2.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory.Comp Formalism.MainNotions.GlobalTheoryTheory.Inhab

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def FinCo {D : D7} {u : D.what₂.Word} (T : Formalism.L2.Forms.Forms0 D u) (B : ColBase D u) : Prop :=
  ∀ w : D.what₂.places.Pl, ∃ γ : (D.mem u).C.cls 0 → D.what₂.Tau → Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.what₂.LL,
    (∀ c τ, flipTwoThree.LocBasis D w (B.Q c τ) (B.eQ c τ) (γ c τ)) ∧
    ∀ x, x ∈ locW D.what₂.places w ((D.fm u).lat 0).L ↔
      ∀ c, flipTwoThree.actAll ((D.fm u).lam 0) (fun τ => (γ c τ)⁻¹) (coT T (gC B) x c) ∈ flipTwoThree.IntSpanAt D w ((D.fm u).lam 0)

theorem colRest_of_fin {D : D7} (F : Formalism.L2.Forms.ColsTiedSym D) (h3 : flipTwoThree.adm3 D) (u : D.what₂.Word) (B : ColBase D u)
    (hB : B.rho = rhoC D) (hfin : FinCo (F.forms u).to0 B) : ColRest B := by
  have hst : ∀ c, Subsingleton ((D.mem u).C.stab 0 c) := by
    exact h3 u
  have hne : Nonempty ((D.mem u).C.cls 0) := classes_level_zero_nonempty F u
  exact ⟨coT (F.forms u).to0 (gC B), coT_injective (T := (F.forms u).to0) _, coT_range (T := (F.forms u).to0) hst _,
    hfin, inf_coT (T := (F.forms u).to0) (B := B) hB hst hne⟩

theorem colValOfTiedS_of_fin
    (h : ∀ D : D7, ∀ F : Formalism.L2.Forms.ColsTiedSym D, flipTwoThree.adm3 D → ∀ (u : D.what₂.Word) (B : ColBase D u),
      B.rho = rhoC D → FinCo (F.forms u).to0 B) :
    Formalism.MainNotions.RT.ColumnValuationFromTwistCompatibility :=
  colValOfTiedS_of_rest' fun D F h3 u => ⟨rhoC D, fun B hB => colRest_of_fin F h3 u B hB (h D F h3 u B hB)⟩

end Formalism.L2.GlobalTheoryTheory.ColValS
