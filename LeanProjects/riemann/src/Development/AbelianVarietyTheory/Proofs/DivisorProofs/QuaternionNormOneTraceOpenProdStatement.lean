import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuaternionNormOneTraceOpenProd
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceOpen
open NumberField IsDedekindDomain GlobalTheory.QSA
open scoped Quaternion Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quaternionNormOneTraceOpen_prod : ∀ (R₁ R₂ : Type) [CommRing R₁] [TopologicalSpace R₁] [CommRing R₂] [TopologicalSpace R₂] (a₁ b₁ : R₁) (a₂ b₂ : R₂), TraceOpen R₁ a₁ b₁ → TraceOpen R₂ a₂ b₂ → TraceOpen (R₁ × R₂) (a₁, a₂) (b₁, b₂) := by
  first | exact @GlobalTheory.QSA.traceOpen_prod | exact GlobalTheory.QSA.traceOpen_prod | (intros; apply GlobalTheory.QSA.traceOpen_prod <;> assumption)
