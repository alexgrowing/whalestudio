import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzSpanLocalTensors
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocFieldLP
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.LiftPair
open scoped Matrix TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartz_span_local_tensors : ∀ (F : Type) [Field F] [NumberField F] (v : Pl F) (κ : Type) [Fintype κ], schA F κ ≤ Submodule.span ℂ {Φ | ∃ (φ : (κ → Fv F v) → ℂ) (r : (κ → AF F) → ℂ), φ ∈ SB (κ → Fv F v) ∧ (∀ φ' ∈ SB (κ → Fv F v), Rest (evFin F v) φ' r) ∧ Φ = tens (evFin F v) φ r} := by
  first | exact @GlobalTheory.PureAtPlace.schA_le_span_tens | exact GlobalTheory.PureAtPlace.schA_le_span_tens | (intros; apply GlobalTheory.PureAtPlace.schA_le_span_tens <;> assumption)
