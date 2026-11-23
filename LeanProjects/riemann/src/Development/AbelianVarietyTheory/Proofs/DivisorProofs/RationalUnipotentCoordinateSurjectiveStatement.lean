import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalUnipotentCoordinateSurjective
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoC
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.UnipDom
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rational_unipotent_coordinate_surjective : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (d d₁ : ℕ) (W : Spc F E d) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (r s i₀ i₁ : ℕ), IsCMExt F E σ → W.IsSkew σ B r s → H'.IsAdapted σ B W W₁ i₀ i₁ → ∀ α : Fin d₁ → E, ∃ γ ∈ unip σ W H', γ ∈ ratU σ W.J ∧ coA σ W.J H' γ = fun j => inclR (F := F) (AF F) (α j) := by
  first | exact @GlobalTheory.ThK.UnipDom.RatPt.exists_unip_rat_coA | exact GlobalTheory.ThK.UnipDom.RatPt.exists_unip_rat_coA | (intros; apply GlobalTheory.ThK.UnipDom.RatPt.exists_unip_rat_coA <;> assumption)
