import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralOrIsEmptySubschemeOfPrimeCharts
import Mathlib
open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isIntegral_or_isEmpty_subscheme_of_prime_charts : ∀ (Y : Scheme.{0}) (I : Y.IdealSheafData) (ι : Type) (W : ι → Y.affineOpens), (⨆ a, (W a).1 = ⊤) → (∀ a, I.ideal (W a) = ⊤ ∨ (I.ideal (W a)).IsPrime) → (∀ a b (ha : (I.ideal (W a)).IsPrime), I.ideal (W b) ≠ ⊤ → (W a).2.fromSpec ⟨I.ideal (W a), ha⟩ ∈ (W b).1) → IsIntegral I.subscheme ∨ IsEmpty I.subscheme := by
  first | exact @GlobalTheory.SubschemeIntegral.isIntegral_or_isEmpty_subscheme | exact GlobalTheory.SubschemeIntegral.isIntegral_or_isEmpty_subscheme | (intros; apply GlobalTheory.SubschemeIntegral.isIntegral_or_isEmpty_subscheme <;> assumption)
