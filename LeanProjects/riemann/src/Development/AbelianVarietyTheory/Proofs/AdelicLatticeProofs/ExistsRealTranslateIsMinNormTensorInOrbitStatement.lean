import Mathlib
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsRealTranslateIsMinNormTensorInOrbit
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.AdelicPair
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_real_translate_isMinNormTensorInOrbit : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (m : ℕ) (d : Fin m → ℕ) (t : TIdx ι d → ℝ), (∃ w ∈ orb d (fun k => (t k : ℂ)), IsMinVec d w) → ∃ g : Matrix ι ι ℝ, g.det = 1 ∧ IsMinVec d (act d (fun k => (t k : ℂ)) (g.map (fun r : ℝ => (r : ℂ)))) := by
  first | exact @GlobalTheory.ClassFin.exists_real_translate_isMinVec | exact GlobalTheory.ClassFin.exists_real_translate_isMinVec | (intros; apply GlobalTheory.ClassFin.exists_real_translate_isMinVec <;> assumption)
