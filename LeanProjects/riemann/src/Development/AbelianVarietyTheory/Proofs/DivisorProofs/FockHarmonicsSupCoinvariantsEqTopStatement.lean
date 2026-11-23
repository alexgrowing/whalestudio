import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockHarmonicsSupCoinvariantsEqTop
import Development.AbelianVarietyTheory.Definitions.Divisors.ActAtApply
open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockHarmonics_sup_coinvariants_eq_top : ∀ (P Q R S : ℕ) (x : ℂ), Submodule.span ℂ (harm2 P Q R S) ⊔ coinv P Q R S x = ⊤ := by
  first | exact @GlobalTheory.HoweR.span_harm2_sup_coinv_eq_univ | exact GlobalTheory.HoweR.span_harm2_sup_coinv_eq_univ | (intros; apply GlobalTheory.HoweR.span_harm2_sup_coinv_eq_univ <;> assumption)
