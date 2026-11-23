import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStandardArchimedeanAddCharOfIsStandardTraceAde
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTransportF
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdeleJoinZero
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isStandardArchimedeanAddChar_of_isStandardTraceAdelic : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ → GlobalTheory.WeilL2Words.IsStdInf F ψ := by
  first | exact @GlobalTheory.WeilL2Words.StdArch.isStdInf_of_isStd | exact GlobalTheory.WeilL2Words.StdArch.isStdInf_of_isStd | (intros; apply GlobalTheory.WeilL2Words.StdArch.isStdInf_of_isStd <;> assumption)
