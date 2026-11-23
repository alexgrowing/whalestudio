import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAdelicPointEqRealMulFiniteBothOrders
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InfPartFPlaceIdem
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryAdelicPoint_eq_real_mul_finite_both_orders : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ)
    (J : Matrix (Fin n) (Fin n) E) (p : GAF σ J), ∃ a ∈ GlobalTheory.WeilPartsF.GinfCF σ J, ∃ k ∈ GlobalTheory.WeilPartsF.GfCF σ J, p = a * k ∧ p = k * a := by
  first | exact @GlobalTheory.WeilPartsF.exists_real_finite_mul | exact GlobalTheory.WeilPartsF.exists_real_finite_mul | (intros; apply GlobalTheory.WeilPartsF.exists_real_finite_mul <;> assumption)
