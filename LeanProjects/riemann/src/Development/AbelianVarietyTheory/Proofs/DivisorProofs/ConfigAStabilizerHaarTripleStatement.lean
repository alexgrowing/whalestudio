import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigAStabilizerHaarTriple
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConeEvFun
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.LemF
open GlobalTheory.Doubling (absE)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.config_a_stabilizer_haar_triple : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (b a' : ℕ)
    (G : Geo σ (b + 2) a') (G₁ : Geo σ b a') (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' →
    ∀ (K : Subgroup (UA σ G.V.J)), IsStab B K → ∀ X om om' om₁ om₁', IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ (v : Pl F) (μK : Measure (KAt K (evFin F v))) (μ : Measure (idelesAt E (evFin F v))), μK.IsHaarMeasure →
      μ.IsHaarMeasure → ∀ m : (AE F E)ˣ → UA σ G.V.J,
      (∀ t ∈ idelesAt E (evFin F v), IsLevi H t (1 : UA σ G₁.V.J) (m t) ∧ m t ∈ UAt σ G.V (evFin F v)) →
      ∀ f : UA σ G.V.J → ℂ,
      (∀ q ∈ UAt σ G.V (evFin F v), mat q *ᵥ incV F H.x = incV F H.x → ∀ x ∈ UAt σ G.V (evFin F v), f (q * x) = f x) →
      Continuous (fun x : UAtSub σ G.V (evFin F v) => f x.1) →
      (∀ g ∈ UAt σ G.V (evFin F v), Integrable (fun p : KAt K (evFin F v) × idelesAt E (evFin F v) =>
          f ((m p.2.1)⁻¹ * p.1.1 * g) * ((absE F E p.2.1 : ℝ) : ℂ) ^ (b + 1)) (μK.prod μ)) →
      ∀ g ∈ UAt σ G.V (evFin F v),
        ∫ k, ∫ t, f ((m t.1)⁻¹ * k.1 * g) * ((absE F E t.1 : ℝ) : ℂ) ^ (b + 1) ∂μ ∂μK =
          ∫ k, ∫ t, f ((m t.1)⁻¹ * k.1) * ((absE F E t.1 : ℝ) : ℂ) ^ (b + 1) ∂μ ∂μK := by
  first | exact @GlobalTheory.ThK.LemF.QuotInv.quotInv | exact GlobalTheory.ThK.LemF.QuotInv.quotInv | (intros; apply GlobalTheory.ThK.LemF.QuotInv.quotInv <;> assumption)
