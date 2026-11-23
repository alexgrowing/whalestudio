import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TraceFormRealCoordinatesIntegralGram
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsRealCoord
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.AdelicPair
open NumberField Matrix Formalism.MainNotions.S GlobalTheory.CuspGeo GlobalTheory.ClassFin
open scoped Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.traceForm_real_coordinates_integral_gram : ∀ (I : AutInst) (N : ℕ) (ρ : (InfinitePlace I.F → Fin I.n → ℂ) ≃ₗ[ℝ] (Fin N → ℝ)), IsRealCoord I ρ → ∃ (X : Matrix (Fin N) (Fin N) ℝ) (μ : ℝ) (c : ℕ), μ ≠ 0 ∧ 1 ≤ c ∧ ∀ (y : I.Ginf) (e : Fin N → Fin I.n → I.E), IsZBasis I e → ∃ B B' : Matrix (Fin N) (Fin N) ℤ, B.map (Int.cast : ℤ → ℝ) = (gm I ρ y e)ᵀ * X * gm I ρ y e ∧ gm I ρ y e * B'.map (Int.cast : ℤ → ℝ) * (gm I ρ y e)ᵀ = μ • X ∧ ∀ i j, (B i j : ℚ) = c * trForm I (e i) (e j) := by
  first | exact @GlobalTheory.CuspGeo.TrReal.trace_form_real_coord | exact GlobalTheory.CuspGeo.TrReal.trace_form_real_coord | (intros; apply GlobalTheory.CuspGeo.TrReal.trace_form_real_coord <;> assumption)
