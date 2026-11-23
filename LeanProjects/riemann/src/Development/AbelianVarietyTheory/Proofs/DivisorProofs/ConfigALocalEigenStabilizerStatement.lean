import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigALocalEigenStabilizer
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConeEvFun
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.LemF
open GlobalTheory.Doubling (absE)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.config_a_local_eigen_stabilizer : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (b a' : ℕ)
    (G : Geo σ (b + 2) a') (G₁ : Geo σ b a') (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' →
    ∀ e, IsEv B G.M G₁.M H.ι H'.ι (isoA H H') e → ∀ ei ev, IsLocPart G.M G₁.M e ei ev →
    ∀ (K : Subgroup (UA σ G.V.J)), IsStab B K → ∀ X om om' om₁ om₁', IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ (v : Pl F) (μK : Measure (KAt K (evFin F v))) (μ : Measure (idelesAt E (evFin F v))), μK.IsHaarMeasure →
      μ.IsHaarMeasure → ∃ m : (AE F E)ˣ → UA σ G.V.J,
      (∀ t ∈ idelesAt E (evFin F v), IsLevi H t (1 : UA σ G₁.V.J) (m t) ∧ m t ∈ UAt σ G.V (evFin F v)) ∧
      ∀ (l : ((Fin b × Fin (b + a') → Fv F v) → ℂ) →ₗ[ℂ] ℂ), ∀ φ ∈ SB (Fin (b + 2) × Fin (b + 2 + a') → Fv F v),
        Integrable (fun p : KAt K (evFin F v) × idelesAt E (evFin F v) =>
          coneEvFun B G H H' om v (ev v) l φ ((m p.2.1)⁻¹ * p.1.1) * ((absE F E p.2.1 : ℝ) : ℂ) ^ (b + 1)) (μK.prod μ) ∧
        l (coneFin B G.M om v (ev v) K μK μ (shiftA H H') X.ν ((b + 2 - a') / 2) φ) =
          ∫ k, ∫ t, coneEvFun B G H H' om v (ev v) l φ ((m t.1)⁻¹ * k.1) * ((absE F E t.1 : ℝ) : ℂ) ^ (b + 1) ∂μ ∂μK := by
  first | exact @GlobalTheory.ConeLeviInt.cone_as_integral | exact GlobalTheory.ConeLeviInt.cone_as_integral | (intros; apply GlobalTheory.ConeLeviInt.cone_as_integral <;> assumption)
