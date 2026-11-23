import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IwasawaDecompositionUpperTriangular
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.InstBorelGL
open MeasureTheory Matrix GlobalTheory.CompanionTheory.QL
open scoped ComplexConjugate ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.iwasawa_decomposition_upperTriangular : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] {O : Subring F} {ϖ : F} {nrm : AbsoluteValue F ℝ} {q : ℕ}, LF O ϖ nrm q → ∀ (n : ℕ) (g : GL (Fin n) F), ∃ b : GL (Fin n) F, (b : Matrix (Fin n) (Fin n) F).BlockTriangular id ∧ ∃ k ∈ GLint O n, g = b * k := by
  first | exact @GlobalTheory.CompanionTheory.QL.Iwasawa.exists_upper_mul_int | exact GlobalTheory.CompanionTheory.QL.Iwasawa.exists_upper_mul_int | (intros; apply GlobalTheory.CompanionTheory.QL.Iwasawa.exists_upper_mul_int <;> assumption)
