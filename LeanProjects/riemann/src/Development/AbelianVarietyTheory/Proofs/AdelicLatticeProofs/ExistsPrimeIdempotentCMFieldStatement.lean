import Mathlib
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsPrimeIdempotentCMField
import Formalism.UnipotentAdelicQuotients.ThmBInHecke
open NumberField IsDedekindDomain NumberField.mixedEmbedding Complex Classical HeckeCharacterZeroLocus.ThmBIn
open scoped TensorProduct ContDiff nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_primeIdempotent_CMField : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ P : HeightOneSpectrum (𝓞 E), ∃ e f, IsPrimeIdem σ P e f := by
  first | exact @GlobalTheory.PrimeIdemExists.exists_isPrimeIdem | exact GlobalTheory.PrimeIdemExists.exists_isPrimeIdem | (intros; apply GlobalTheory.PrimeIdemExists.exists_isPrimeIdem <;> assumption)
