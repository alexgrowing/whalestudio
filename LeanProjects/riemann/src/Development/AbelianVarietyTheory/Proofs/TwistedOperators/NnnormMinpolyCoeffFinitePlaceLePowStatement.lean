import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NnnormMinpolyCoeffFinitePlaceLePow
import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OneLeHtE

open NumberField IsDedekindDomain GlobalTheory.AdelicU
open scoped TensorProduct NNReal
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nnnorm_minpoly_coeff_finitePlace_le_pow : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (x : E) (v : HeightOneSpectrum (𝓞 F)) (j : ℕ), ‖algebraMap F (v.adicCompletion F) ((minpoly F x).coeff j)‖₊ ≤ max 1 (absFin F v ((1 : v.adicCompletion F) ⊗ₜ[F] x)) ^ Module.finrank F E := by
  first | exact @GlobalTheory.CoefHeight.nnnorm_coeff_minpoly_le | exact GlobalTheory.CoefHeight.nnnorm_coeff_minpoly_le | (intros; apply GlobalTheory.CoefHeight.nnnorm_coeff_minpoly_le <;> assumption)
