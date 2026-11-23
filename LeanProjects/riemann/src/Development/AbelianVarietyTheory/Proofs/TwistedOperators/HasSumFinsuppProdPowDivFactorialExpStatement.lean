import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasSumFinsuppProdPowDivFactorialExp
import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjMono
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FockTransl
open Formalism.L2.Ker (VCx DVar derivAt0)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasSum_finsupp_prod_pow_div_factorial_exp_sum : ∀ (κ : Type) [Fintype κ] (x : κ → ℂ), HasSum (fun m : κ →₀ ℕ => m.prod fun k n => x k ^ n / (n.factorial : ℂ)) (Complex.exp (∑ k, x k)) := by
  first | exact @GlobalTheory.hasSum_finsupp_prod_pow_div_factorial_exp | exact GlobalTheory.hasSum_finsupp_prod_pow_div_factorial_exp | (intros; apply GlobalTheory.hasSum_finsupp_prod_pow_div_factorial_exp <;> assumption)
