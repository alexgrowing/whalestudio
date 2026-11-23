import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ProductLocalDensitiesAdeleCharacter
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.LocalDualIndex
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.LocalDualIndex
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.product_localDensities_adeleCharacter : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E] (σ : E →ₐ[F] E), IsCMExt F E σ → (∀ x : E, star x = σ x) → Formalism.HermitianLatticesTheory.IsCMUnram E → ∀ ψ, IsCharAF F ψ → (∀ v, (intV F v).relIndex (dualV F ψ v) ≠ 0 ∧ (dualV F ψ v).relIndex (intV F v) ≠ 0) ∧ ∀ a : F, a ≠ 0 → IsScalingInf F ψ a → ∀ M : ℕ, 2 ≤ M → Summable (fun v => |localDensity F E ψ M v - 1|) ∧ ∃ P : ℝ, 0 < P ∧ HasProd (localDensity F E ψ M) P ∧ absInf F a ^ ((M : ℝ) - 1 / 2) * P = absDiscr F ^ ((1 : ℝ) / 2 - M) / Formalism.HermitianLatticesTheory.lValEta E M := by
  first | exact @GlobalTheory.LocalDensityProduct.density_product | exact GlobalTheory.LocalDensityProduct.density_product | (intros; apply GlobalTheory.LocalDensityProduct.density_product <;> assumption)
