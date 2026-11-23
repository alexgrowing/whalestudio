import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmTypeFromConjugateComplement
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsRestFurther
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.FWT GlobalTheory.CovTop
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cm_type_from_conjugate_complement : ∀ D : D7, letI : IsCMField D.host.E := D.host.isCMField_hostE; (∀ τ : D.host.E →+* ℂ, τ ∈ GlobalTheory.MassLink.psi D ↔ ComplexEmbedding.conjugate τ ∉ GlobalTheory.MassLink.psi D) ∧ ∃ eΨ : D.what₂.Tau ≃ GlobalTheory.MassLink.psi D, ∀ ρ, ((eΨ ρ : GlobalTheory.MassLink.psi D) : D.host.E →+* ℂ) = TH.tauE D ρ := by
  first | exact @GlobalTheory.MassLink.psi_cmType_equiv | exact GlobalTheory.MassLink.psi_cmType_equiv | (intros; apply GlobalTheory.MassLink.psi_cmType_equiv <;> assumption)
