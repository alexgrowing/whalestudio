import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InfinitePlaceMinpolyCoeffLePowMaxEmbeddings
import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OneLeHtE

open NumberField IsDedekindDomain GlobalTheory.AdelicU
open scoped TensorProduct NNReal
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.infinitePlace_minpoly_coeff_le_pow_max_embeddings : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (x : E) (w : InfinitePlace F) (j : ℕ), w ((minpoly F x).coeff j) ≤ 2 ^ Module.finrank F E * ((max 1 (Finset.univ.sup fun τ : EmbOver E w => ‖τ.1 x‖₊) : ℝ≥0) : ℝ) ^ Module.finrank F E := by
  first | exact @GlobalTheory.minpoly_coeff_le_inf | exact GlobalTheory.minpoly_coeff_le_inf | (intros; apply GlobalTheory.minpoly_coeff_le_inf <;> assumption)
