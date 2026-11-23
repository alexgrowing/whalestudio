import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.MemIntegralGLIffIntegralUnitDet
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.InstBorelGL
open MeasureTheory Matrix GlobalTheory.CompanionTheory.QL
open scoped ComplexConjugate ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_integralGL_iff_integral_unit_det : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] {O : Subring F} {ϖ : F} {nrm : AbsoluteValue F ℝ} {q : ℕ}, LF O ϖ nrm q → ∀ (n : ℕ) (g : GL (Fin n) F), g ∈ GLint O n ↔ (IsInt O (g : Matrix (Fin n) (Fin n) F) ∧ nrm (g : Matrix (Fin n) (Fin n) F).det = 1) := by
  first | exact @GlobalTheory.CompanionTheory.QLDet.mem_GLint_iff | exact GlobalTheory.CompanionTheory.QLDet.mem_GLint_iff | (intros; apply GlobalTheory.CompanionTheory.QLDet.mem_GLint_iff <;> assumption)
