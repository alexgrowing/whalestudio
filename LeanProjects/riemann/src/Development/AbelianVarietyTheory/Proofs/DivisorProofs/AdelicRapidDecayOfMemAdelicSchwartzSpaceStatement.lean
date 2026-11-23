import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicRapidDecayOfMemAdelicSchwartzSpace
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoMulInvOf

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SWQ GlobalTheory.ThetaTransform
open scoped Matrix Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicRapidDecay_of_mem_adelicSchwartzSpace : ∀ (F : Type) [Field F] [NumberField F] (N : ℕ), ∀ Φ ∈ GlobalTheory.WeilM.schA F (Fin N), Decay Φ := by
  first | exact @GlobalTheory.SchwartzDecay.decay_of_mem_schA | exact GlobalTheory.SchwartzDecay.decay_of_mem_schA | (intros; apply GlobalTheory.SchwartzDecay.decay_of_mem_schA <;> assumption)
