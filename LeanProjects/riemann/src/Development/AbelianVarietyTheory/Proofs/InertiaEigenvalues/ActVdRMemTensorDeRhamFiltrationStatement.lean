import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ActVdRMemTensorDeRhamFiltration
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.Pst GlobalTheory.PMon TensorProduct Module
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.actVdR_mem_tensorDeRhamFiltration : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (V : Type) [AddCommGroup V] [Module ℚ_[l] V] (ρ : Representation ℚ_[l] ↥(GK K) V) (a : ℤ) (g : ↥(GK K)) (y : V ⊗[ℚ_[l]] P.R.BdR), y ∈ FilV (P.PD K) (LL := ℚ_[l]) (V := V) a → actVdR (P.PD K) ρ g y ∈ FilV (P.PD K) (LL := ℚ_[l]) (V := V) a := by
  first | exact @GlobalTheory.FilStable.actVdR_mem_FilV | exact GlobalTheory.FilStable.actVdR_mem_FilV | (intros; apply GlobalTheory.FilStable.actVdR_mem_FilV <;> assumption)
