import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPlaneSkewIdealCoprimeLt
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocCharEqValZpow
open NumberField IsDedekindDomain GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.UnrEuler Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped nonZeroDivisors
open Formalism.L2.Host (aboveF)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adapted_plane_skew_ideal_coprime_lt : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) {n n₁ : ℕ} (H : Plane E n n₁) (Y : Spc F E n) (Y₁ : Spc F E n₁) (i₀ i₁ r s : ℕ), B.IsGood σ → Y.IsSkew σ B r s → H.IsAdapted σ B Y Y₁ i₀ i₁ → i₀ < i₁ → i₁ < n → H.𝔟 ≠ 0 ∧ ∀ v ∈ B.P, ∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) = v → FractionalIdeal.count E w H.𝔟 = 0 := by
  first | exact @GlobalTheory.PlaneSkewIdeal.ideal_ne_zero_and_count_eq_zero | exact GlobalTheory.PlaneSkewIdeal.ideal_ne_zero_and_count_eq_zero | (intros; apply GlobalTheory.PlaneSkewIdeal.ideal_ne_zero_and_count_eq_zero <;> assumption)
