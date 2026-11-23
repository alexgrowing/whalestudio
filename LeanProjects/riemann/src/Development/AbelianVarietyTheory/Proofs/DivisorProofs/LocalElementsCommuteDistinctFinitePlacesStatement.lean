import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalElementsCommuteDistinctFinitePlaces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClassesAt
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.FrameOf
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localElements_commute_distinct_realPlaces : ∀ {D : D7} (V : Formalism.BasicNotions.TH.HSp D) {Pl0 : Type} (pl : Pl0 → Pl D.host.E) (ok : Set Pl0) (i i' : ok × ℕ) (x y : Bridge.Gf V), (pl i.1).under (𝓞 D.host.F) ≠ (pl i'.1).under (𝓞 D.host.F) → isLocEnv V pl ok i x → isLocEnv V pl ok i' y → x * y = y * x := by
  first | exact @GlobalTheory.LocComm.mul_comm_of_isLocEnv | exact GlobalTheory.LocComm.mul_comm_of_isLocEnv | (intros; apply GlobalTheory.LocComm.mul_comm_of_isLocEnv <;> assumption)
