import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsLogDerivQExpansionModPrimePowHeckeNorm
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsRootOfIsAlgClosed
import Development.AbelianVarietyTheory.Definitions.Foundations.EeProd
open GlobalTheory.KZ GlobalTheory.CyclotomicQExpansion GlobalTheory.Glue
open scoped MatrixGroups
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isLogDerivQExpansionModPrimePow_heckeNorm : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosed Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (A : ValuationSubring Ω) (l : ℕ) [Fact l.Prime] (n : ℕ) (f : X.K) (φ : HahnSeries ℚ Ω),
  X.sl (ofSL ModularGroup.T) f = f → (∀ r : ℚ, φ.coeff r ≠ 0 → r.den = 1) → IsDl X A l n 1 f φ →
  IsDl X A l n 1 (∏ j ∈ Finset.range l, X.sl (toGQ !![1, (j : ℤ); 0, (l : ℤ)]) f) (hq ε l φ) := by
  first | exact @GlobalTheory.NormDl.isDl_norm | exact GlobalTheory.NormDl.isDl_norm | (intros; apply GlobalTheory.NormDl.isDl_norm <;> assumption)
