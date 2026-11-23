import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceCharacterAnnihilatorCompact
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UAtMemIsoB
open MeasureTheory Filter NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ConeSoB
open scoped TensorProduct GlobalTheory.VacAny
open Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trace_character_annihilator_compact : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (v : Pl F) (ψ : AddChar (Fv F v) ℂ),
    Continuous ψ → ψ ≠ 1 → ∀ U ∈ nhds (0 : Fv F v ⊗[F] E),
      IsCompact {l : Fv F v ⊗[F] E | ∀ t ∈ U, ψ (Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (t * l)) = 1} := by
  first | exact @GlobalTheory.TraceAnnCompact.isCompact_trace_ann | exact GlobalTheory.TraceAnnCompact.isCompact_trace_ann | (intros; apply GlobalTheory.TraceAnnCompact.isCompact_trace_ann <;> assumption)
