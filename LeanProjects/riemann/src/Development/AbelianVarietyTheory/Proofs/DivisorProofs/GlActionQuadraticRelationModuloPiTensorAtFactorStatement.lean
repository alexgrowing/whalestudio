import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlActionQuadraticRelationModuloPiTensorAtFactor
import Development.AbelianVarietyTheory.Definitions.Divisors.ActAtApply
open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.glActionQuadraticRelationModulo_piTensorAtFactor : ∀ (T : Type) [Fintype T] [DecidableEq T] (V : T → Type) [∀ w, AddCommGroup (V w)] [∀ w, Module ℂ (V w)], ∀ (C : ∀ w, Submodule ℂ (V w)) (w : T) (p q : ℕ) (a : Mat p q →ₗ[ℂ] Module.End ℂ (V w)) (α β α' β' : ℂ), QuadMod a α β α' β' (C w) ⊤ → QuadMod (actAt w a) α β α' β' (tensAny C) ⊤ := by
  first | exact @GlobalTheory.HoweR.quadMod_actAt | exact GlobalTheory.HoweR.quadMod_actAt | (intros; apply GlobalTheory.HoweR.quadMod_actAt <;> assumption)
