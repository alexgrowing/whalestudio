import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FinprodLocalDifferentIdealNormEqDiscr
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.LocalDualIndex
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.LocalDualIndex
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finprod_localDifferentIdealNorm_eq_discr : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E] (σ : E →ₐ[F] E), IsCMExt F E σ → (∀ x : E, star x = σ x) → Formalism.HermitianLatticesTheory.IsCMUnram E → (Function.mulSupport (normDifferentV F)).Finite ∧ ((∏ᶠ v, normDifferentV F v : ℕ) : ℝ) = absDiscr F ∧ absDiscr F = (2 * Formalism.HermitianLatticesTheory.vInv E) ^ Formalism.HermitianLatticesTheory.fDeg E := by
  first | exact @GlobalTheory.LocalDifferentProduct.prod_normDifferentV | exact GlobalTheory.LocalDifferentProduct.prod_normDifferentV | (intros; apply GlobalTheory.LocalDifferentProduct.prod_normDifferentV <;> assumption)
