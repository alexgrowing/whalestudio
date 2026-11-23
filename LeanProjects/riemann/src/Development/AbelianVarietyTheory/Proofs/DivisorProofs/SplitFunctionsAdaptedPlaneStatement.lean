import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitFunctionsAdaptedPlane
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.split_functions_adapted_plane : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (W : Spc F E (a + a')) (d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E (a + a') d₁) (i₀ i₁ r s r₁ s₁ : ℕ) (X : Chars F E), B.IsGood σ → a' < a → W.IsSkew σ B r s → W₁.IsSkew σ B r₁ s₁ → H'.IsAdapted σ B W W₁ i₀ i₁ → ∀ f fa fb fa' fb' : UA σ W.J → ℂ, Split2 W₁ H' X f fa fb → Split2 W₁ H' X f fa' fb' → fa = fa' ∧ fb = fb' := by
  first | exact @GlobalTheory.SplitUniq.split2_unique_skew | exact GlobalTheory.SplitUniq.split2_unique_skew | (intros; apply GlobalTheory.SplitUniq.split2_unique_skew <;> assumption)
