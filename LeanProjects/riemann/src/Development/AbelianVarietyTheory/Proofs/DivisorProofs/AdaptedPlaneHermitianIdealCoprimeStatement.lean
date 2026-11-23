import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPlaneHermitianIdealCoprime
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
open NumberField IsDedekindDomain GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adapted_plane_hermitian_ideal_coprime : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) {n n₁ : ℕ} (H : Plane E n n₁) (Y : Spc F E n) (Y₁ : Spc F E n₁) (i₀ i₁ r s : ℕ),
    B.IsGood σ → Y.IsHerm σ B r s → H.IsAdapted σ B Y Y₁ i₀ i₁ → i₀ < n → i₁ < n →
    H.𝔟 ≠ 0 ∧ ∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) ∈ B.P → FractionalIdeal.count E w H.𝔟 = 0 := by
  first | exact @GlobalTheory.AdaptedPlaneIdeal.ideal_ne_zero_and_count_eq_zero | exact GlobalTheory.AdaptedPlaneIdeal.ideal_ne_zero_and_count_eq_zero | (intros; apply GlobalTheory.AdaptedPlaneIdeal.ideal_ne_zero_and_count_eq_zero <;> assumption)
