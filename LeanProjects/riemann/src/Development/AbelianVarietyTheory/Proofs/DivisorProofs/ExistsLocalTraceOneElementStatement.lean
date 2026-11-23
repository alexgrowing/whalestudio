import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalTraceOneElement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntLocConjIntLocConj
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix
open scoped TensorProduct
open GlobalTheory.TamSU GlobalTheory.SUVol GlobalTheory.UCls GlobalTheory.AdelicU GlobalTheory.TamOne
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_local_trace_one_element : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ v : HeightOneSpectrum (𝓞 (maximalRealSubfield E)), ∃ w : intLoc (maximalRealSubfield E) E v, w + intLocConj v w = 1 := by
  first | exact @GlobalTheory.TamOne.exists_add_intLocConj_eq_one | exact GlobalTheory.TamOne.exists_add_intLocConj_eq_one | (intros; apply GlobalTheory.TamOne.exists_add_intLocConj_eq_one <;> assumption)
