import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NegTransposeFockSecondActionQuadraticModCoinvari
import Development.AbelianVarietyTheory.Definitions.Divisors.ActAtApply
open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.negTranspose_fockSecondAction_quadratic_mod_coinvariants : ∀ (P Q R S : ℕ) (x : ℂ), ∃ α β : ℂ, ∀ a b f, qop (negT (units (fockAct2 P Q R S))) α β a b f ∈ coinv P Q R S x := by
  first | exact @GlobalTheory.HoweR.QuadT.negT_fockAct2_quad | exact GlobalTheory.HoweR.QuadT.negT_fockAct2_quad | (intros; apply GlobalTheory.HoweR.QuadT.negT_fockAct2_quad <;> assumption)
