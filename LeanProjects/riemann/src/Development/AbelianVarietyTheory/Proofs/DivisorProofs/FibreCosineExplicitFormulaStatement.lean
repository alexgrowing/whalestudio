import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibreCosineExplicitFormula
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FsOne
open MeasureTheory
open scoped ComplexOrder ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fibre_cosine_explicit_formula : ∀ (G : Matrix (Fin 2) (Fin 2) ℂ), G.PosDef → ∀ x : ℂ, 1 + G 1 0 / G 0 0 * x ≠ 0 →
    GlobalTheory.FibCos.cos G x = 1 / (1 + ‖(Real.sqrt G.det.re / (G 0 0).re : ℂ) * x / (1 + G 1 0 / G 0 0 * x)‖ ^ 2) ∧
    GlobalTheory.FibCos.fs G x = ‖(Real.sqrt G.det.re / (G 0 0).re : ℂ) / (1 + G 1 0 / G 0 0 * x) ^ 2‖ ^ 2 *
      (1 / (Real.pi * (1 + ‖(Real.sqrt G.det.re / (G 0 0).re : ℂ) * x / (1 + G 1 0 / G 0 0 * x)‖ ^ 2) ^ 2)) := by
  first | exact @GlobalTheory.FibCos.cos_fs_moebius | exact GlobalTheory.FibCos.cos_fs_moebius | (intros; apply GlobalTheory.FibCos.cos_fs_moebius <;> assumption)
