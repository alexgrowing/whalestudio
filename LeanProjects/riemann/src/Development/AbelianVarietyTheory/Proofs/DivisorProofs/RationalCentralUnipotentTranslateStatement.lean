import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalCentralUnipotentTranslate
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoC
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.UnipDom
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rational_central_unipotent_translate : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (d d₁ : ℕ) (W : Spc F E d) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (r s i₀ i₁ : ℕ), IsCMExt F E σ → W.IsSkew σ B r s → H'.IsAdapted σ B W W₁ i₀ i₁ → ∀ q : F, ∃ γ ∈ unip σ W H', γ ∈ ratU σ W.J ∧ ∀ u ∈ unip σ W H', coA σ W.J H' (γ * u) = coA σ W.J H' u ∧ coC σ W.J H' (γ * u) = algebraMap (AF F) (AE F E) (algebraMap F (AF F) q) + coC σ W.J H' u := by
  first | exact @GlobalTheory.ThK.UnipDom.RatCentral.exists_rat_translate_coC | exact GlobalTheory.ThK.UnipDom.RatCentral.exists_rat_translate_coC | (intros; apply GlobalTheory.ThK.UnipDom.RatCentral.exists_rat_translate_coC <;> assumption)
