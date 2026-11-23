import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.CartanDecompositionGeneralLinear
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.InstBorelGL
open MeasureTheory Matrix GlobalTheory.CompanionTheory.QL
open scoped ComplexConjugate ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cartan_decomposition_generalLinear : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] {O : Subring F} {ϖ : F} {nrm : AbsoluteValue F ℝ} {q : ℕ}, LF O ϖ nrm q → ∀ (n : ℕ) (g : GL (Fin n) F), ∃ k₁ ∈ GLint O n, ∃ k₂ ∈ GLint O n, ∃ (e : Fin n → ℤ) (d : GL (Fin n) F), (d : Matrix (Fin n) (Fin n) F) = Matrix.diagonal (fun i => ϖ ^ e i) ∧ g = k₁ * d * k₂ := by
  first | exact @GlobalTheory.CompanionTheory.QL.KAK.cartan | exact GlobalTheory.CompanionTheory.QL.KAK.cartan | (intros; apply GlobalTheory.CompanionTheory.QL.KAK.cartan <;> assumption)
