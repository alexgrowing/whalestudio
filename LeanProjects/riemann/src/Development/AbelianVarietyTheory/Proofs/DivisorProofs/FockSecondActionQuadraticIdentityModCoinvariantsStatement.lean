import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockSecondActionQuadraticIdentityModCoinvariants
import Development.AbelianVarietyTheory.Definitions.Divisors.ActAtApply
open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockSecondAction_quadraticIdentity_mod_coinvariants : ∀ (P Q R S : ℕ) (x : ℂ), ∃ α β : ℂ, ∀ a b f, qop (units (fockAct2 P Q R S)) α β a b f ∈ coinv P Q R S x := by
  first | exact @GlobalTheory.HoweR.SecondQuad.qop_mem_coinv | exact GlobalTheory.HoweR.SecondQuad.qop_mem_coinv | (intros; apply GlobalTheory.HoweR.SecondQuad.qop_mem_coinv <;> assumption)
