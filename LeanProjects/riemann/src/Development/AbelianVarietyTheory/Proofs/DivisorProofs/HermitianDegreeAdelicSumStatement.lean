import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianDegreeAdelicSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinPart
open NumberField ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory.LieHt GlobalTheory.LieRead

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_degree_adelic_sum : ∀ (K : Type) [Field K] [NumberField K] (g : ℕ) (L : Submodule (𝓞 K) (Fin g → K)) (h : HermFam K (Fin g → K)), Full L → deg h L = -(adelSum h L) / Module.finrank ℚ K := by
  first | exact @GlobalTheory.LieRead.deg_eq_neg_adelSum_div_finrank | exact GlobalTheory.LieRead.deg_eq_neg_adelSum_div_finrank | (intros; apply GlobalTheory.LieRead.deg_eq_neg_adelSum_div_finrank <;> assumption)
