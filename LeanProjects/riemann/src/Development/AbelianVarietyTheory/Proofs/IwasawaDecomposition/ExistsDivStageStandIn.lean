import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SameForm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LinearIndependentSemilinearOfBasis

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Df

attribute [local instance] GlobalTheory.Mem.Col2.starE

namespace GlobalTheory.Mem.Df

theorem exists_divStage_standIn : ∀ (B : Base) (C : Cols B) (W : RowsRest B C), StandIn W →
    ∀ η : ℝ, ∃ V : DivStage B C W, V.div.etaF = η := by
  intro B C W _ η
  obtain ⟨V, -, -, -, -, -, -, -, hη, -⟩ := GlobalTheory.Mem.exists_divStage B C W W.Drows W.onb.toBasis (fun _ => 1)
    (fun _ => by simp) ⊤ (fun u => ((C.fm u).lat 0).L) (fun _ => 0) (fun _ => 0) η
  exact ⟨V, hη⟩

end GlobalTheory.Mem.Df
