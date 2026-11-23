import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemSpanTprodOfCommuteAtEachPlace
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EvalAtOneExtremalMul
open MvPolynomial Formalism.BasicNotions Formalism.L2.Forms Formalism.L2.Ker GlobalTheory.KJInf MeasureTheory
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_span_tprod_of_commute_at_each_place : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (V W : ι → Type) [∀ τ, AddCommGroup (V τ)] [∀ τ, Module ℂ (V τ)] [∀ τ, AddCommGroup (W τ)] [∀ τ, Module ℂ (W τ)] [∀ τ, FiniteDimensional ℂ (V τ)] (R : ∀ τ, Set ((V τ →ₗ[ℂ] V τ) × (W τ →ₗ[ℂ] W τ))) (Q : PiTensorProduct ℂ V →ₗ[ℂ] PiTensorProduct ℂ W), (∀ τ, ∀ p ∈ R τ, Q ∘ₗ PiTensorProduct.map (Function.update (fun σ => (LinearMap.id : V σ →ₗ[ℂ] V σ)) τ p.1) = PiTensorProduct.map (Function.update (fun σ => (LinearMap.id : W σ →ₗ[ℂ] W σ)) τ p.2) ∘ₗ Q) → Q ∈ Submodule.span ℂ {T | ∃ t : ∀ τ, V τ →ₗ[ℂ] W τ, (∀ τ, ∀ p ∈ R τ, t τ ∘ₗ p.1 = p.2 ∘ₗ t τ) ∧ T = PiTensorProduct.map t} := by
  first | exact @GlobalTheory.PiTensorCommute.mem_span_map_of_commute | exact GlobalTheory.PiTensorCommute.mem_span_map_of_commute | (intros; apply GlobalTheory.PiTensorCommute.mem_span_map_of_commute <;> assumption)
