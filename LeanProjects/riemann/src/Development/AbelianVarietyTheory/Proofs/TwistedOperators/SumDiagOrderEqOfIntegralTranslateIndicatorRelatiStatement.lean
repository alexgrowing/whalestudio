import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SumDiagOrderEqOfIntegralTranslateIndicatorRelati
import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsPairingSingleNe
open Matrix Formalism.UG GlobalTheory.Hk3 GlobalTheory.FinWeil GlobalTheory.SphTheta ValuativeRel Classical
open GlobalTheory.LFun (HasSatU IsSatVecU heckeVec)
open GlobalTheory.LGrp (bcParam extProd)
open GlobalTheory.WeilM (UG IsQuad Darboux symp sbClass SB IsWeilB IsWeilPair TestClass schr dbl diagCols)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalThetaInertPlace (str chi IsUnramAdd)
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_diag_order_eq_of_integralTranslateIndicator_relation : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q : ℕ), IsUnramInv ϖ σ q → ∀ (m : ℕ) (ι κ : Type) [Fintype ι] [Fintype κ] (c : ι → ℂ) (c' : κ → ℂ) (U : ι → GL (Fin m) L) (V : κ → GL (Fin m) L), (∀ i, (U i).1.BlockTriangular id) → (∀ j, (V j).1.BlockTriangular id) → (∀ t : GL (Fin m) L, ∑ i, c i * (if t.1 * (U i).1 ∈ intMat L (Fin m) (Fin m) then 1 else 0) = ∑ j, c' j * (if (V j).1 * t.1 ∈ intMat L (Fin m) (Fin m) then 1 else 0)) → ∀ f : (Fin m → ℤ) → ℂ, ∑ i, c i * f (fun r => ordL ((U i).1 r r)) = ∑ j, c' j * f (fun r => ordL ((V j).1 r.rev r.rev)) := by
  first | exact @GlobalTheory.SphTheta.sum_ordL_diag_eq_of_indicator | exact GlobalTheory.SphTheta.sum_ordL_diag_eq_of_indicator | (intros; apply GlobalTheory.SphTheta.sum_ordL_diag_eq_of_indicator <;> assumption)
