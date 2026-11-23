import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigAHaarStabilizerBis
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocPart
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.LemF
open GlobalTheory.Doubling (absE)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.config_A_haar_stabilizer : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (b a' : ℕ)
    (G : Geo σ (b + 2) a') (G₁ : Geo σ b a') (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' →
    B.IsGood σ → G.IsGood B → G₁.IsGood B →
    ∀ (K : Subgroup (UA σ G.V.J)), IsStab B K → ∀ (μK : Measure (KAt K (evI F))) (μ : Measure (idelesAt E (evI F))),
    μK.IsHaarMeasure → μ.IsHaarMeasure →
    ∀ m : (AE F E)ˣ → UA σ G.V.J, (∀ l ∈ idelesAt E (evI F), IsLevi (W₁ := G₁.V) H l 1 (m l) ∧ m l ∈ UAt σ G.V (evI F)) →
    ∀ L : UA σ G.V.J → ℂ, ContinuousOn L (UAt σ G.V (evI F)) →
    (∀ n ∈ unip σ G.V H, n ∈ UAt σ G.V (evI F) → ∀ x ∈ UAt σ G.V (evI F), L (n * x) = L x) →
    (∀ (g₀ : UA σ G₁.V.J) (g' : UA σ G.V.J), IsLevi H 1 g₀ g' → g' ∈ UAt σ G.V (evI F) → g₀ ∈ UAt σ G₁.V (evI F) →
      ∀ x ∈ UAt σ G.V (evI F), L (g' * x) = L x) →
    (∀ g ∈ UAt σ G.V (evI F), Integrable (fun p : KAt K (evI F) × idelesAt E (evI F) =>
      L (m p.2.1⁻¹ * p.1.1 * g) * (((absE F E p.2.1 : ℝ) ^ ((b + 1 : ℕ) : ℝ) : ℝ) : ℂ)) (μK.prod μ)) →
    ∀ g ∈ UAt σ G.V (evI F),
      ∫ k, ∫ l, L (m l.1⁻¹ * k.1 * g) * (((absE F E l.1 : ℝ) ^ ((b + 1 : ℕ) : ℝ) : ℝ) : ℂ) ∂μ ∂μK =
        ∫ k, ∫ l, L (m l.1⁻¹ * k.1) * (((absE F E l.1 : ℝ) ^ ((b + 1 : ℕ) : ℝ) : ℝ) : ℂ) ∂μ ∂μK := by
  first | exact @GlobalTheory.IwasawaConeA.kInt_cone_right_inv | exact GlobalTheory.IwasawaConeA.kInt_cone_right_inv | (intros; apply GlobalTheory.IwasawaConeA.kInt_cone_right_inv <;> assumption)
