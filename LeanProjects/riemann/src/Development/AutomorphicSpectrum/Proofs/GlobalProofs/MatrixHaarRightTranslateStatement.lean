import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.MatrixHaarRightTranslate
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.InstBorelGL
open MeasureTheory Matrix GlobalTheory.CompanionTheory.QL
open scoped ComplexConjugate ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.matrix_haar_right_translate : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] {O : Subring F} {ϖ : F} {nrm : AbsoluteValue F ℝ} {q : ℕ}, LF O ϖ nrm q → ∀ n m : ℕ, ∀ (dx : Measure (Matrix (Fin n) (Fin m) F)), dx.IsAddLeftInvariant → dx (intMat O n m) = 1 → (∀ g : GL (Fin m) F, Measure.map (fun x : Matrix (Fin n) (Fin m) F => x * (g : Matrix (Fin m) (Fin m) F)) dx = ENNReal.ofReal ((nrm (g : Matrix (Fin m) (Fin m) F).det)⁻¹ ^ n) • dx) ∧ (∀ k ∈ GLint O n, Measure.map (fun x : Matrix (Fin n) (Fin m) F => (k : Matrix (Fin n) (Fin n) F) * x) dx = dx) := by
  first | exact @GlobalTheory.CompanionTheory.QLScale.haar_mat_scale | exact GlobalTheory.CompanionTheory.QLScale.haar_mat_scale | (intros; apply GlobalTheory.CompanionTheory.QLScale.haar_mat_scale <;> assumption)
