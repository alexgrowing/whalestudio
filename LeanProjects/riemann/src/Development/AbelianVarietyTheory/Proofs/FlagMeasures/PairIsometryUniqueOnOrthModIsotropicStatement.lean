import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.PairIsometryUniqueOnOrthModIsotropic
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.RowMinor
import Formalism.SharpRestriction.CuspSpanNormBounds.CongruenceAtSplitFrobeniusHolds
open NumberField Module Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt GlobalTheory.LoopC
open scoped ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pair_isometry_unique_on_orth_mod_isotropic : ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (S : HSpace E) (r : ℕ) (T T' : E) (Λ : Submodule (𝓞 E) S.V) (g : ℕ) (F : LFlag S r T) (A B : LFlag S r T') (β₁ β₂ : S.V ≃ₗ[E] S.V), Submodule.IsLattice E Λ → Formalism.HermitianLatticesTheory.IsUnimodular S.hT Λ → 3 ≤ g → T' ≠ 0 → (∀ x ∈ orth S (Xplus A), x ∉ Xsp A → 0 < Algebra.trace ℚ E (S.hT x x)) → XLam Λ F ≤ Ideal.span {(g : 𝓞 E)} • Λ ⊔ XLam Λ A → XLam Λ F ≤ Ideal.span {(g : 𝓞 E)} • Λ ⊔ XLam Λ B → IsAutLam S Λ β₁ → (Xsp A).map (β₁ : S.V →ₗ[E] S.V) = Xsp B → β₁ A.fl.z - B.fl.z ∈ Xsp B → IotaCompat Λ F A B β₁ g → IsAutLam S Λ β₂ → (Xsp A).map (β₂ : S.V →ₗ[E] S.V) = Xsp B → β₂ A.fl.z - B.fl.z ∈ Xsp B → IotaCompat Λ F A B β₂ g → ∀ x ∈ orth S (Xsp A), β₁ x - β₂ x ∈ Xsp B := by
  first | exact @GlobalTheory.LoopC.BetaUniq.main | exact GlobalTheory.LoopC.BetaUniq.main | (intros; apply GlobalTheory.LoopC.BetaUniq.main <;> assumption)
