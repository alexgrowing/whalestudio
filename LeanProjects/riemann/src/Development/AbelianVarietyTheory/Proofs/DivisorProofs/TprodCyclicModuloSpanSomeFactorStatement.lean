import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TprodCyclicModuloSpanSomeFactor
import Development.AbelianVarietyTheory.Definitions.Divisors.ActAtApply
open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tprod_cyclic_modulo_spanSomeFactor : ∀ (T : Type) [Fintype T] [DecidableEq T] (V : T → Type) [∀ w, AddCommGroup (V w)] [∀ w, Module ℂ (V w)], ∀ (R S : T → ℕ) (a : ∀ w, Mat (R w) (S w) →ₗ[ℂ] Module.End ℂ (V w)) (C : ∀ w, Submodule ℂ (V w)) (v : ∀ w, V w), (∀ w, genSub (a w) {v w} ⊔ C w = ⊤) → ∀ N : Submodule ℂ (PiTensorProduct ℂ V), (∀ w, Stab (actAt w (a w)) N) → tensAny C ≤ N → PiTensorProduct.tprod ℂ v ∈ N → N = ⊤ := by
  first | exact @GlobalTheory.HoweR.tprod_cyclic_top | exact GlobalTheory.HoweR.tprod_cyclic_top | (intros; apply GlobalTheory.HoweR.tprod_cyclic_top <;> assumption)
