import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeesawTypeALocalPartStabilizer
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConeEvFun
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.LemF
open GlobalTheory.Doubling (absE)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.seesaw_type_a_local_part_stabilizer : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (b a' : ℕ)
    (G : Geo σ (b + 2) a') (G₁ : Geo σ b a') (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' →
    ∀ e, IsEv B G.M G₁.M H.ι H'.ι (isoA H H') e → ∀ ei ev, IsLocPart G.M G₁.M e ei ev →
    ∀ (K : Subgroup (UA σ G.V.J)), IsStab B K → ∀ X om om' om₁ om₁', IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ (v : Pl F) (μK : Measure (KAt K (evFin F v))) (μ : Measure (idelesAt E (evFin F v))), μK.IsHaarMeasure →
      μ.IsHaarMeasure → ∀ φ ∈ SB (Fin (b + 2) × Fin (b + 2 + a') → Fv F v),
      ∀ l : ((Fin b × Fin (b + a') → Fv F v) → ℂ) →ₗ[ℂ] ℂ,
        Integrable (fun p : KAt K (evFin F v) × idelesAt E (evFin F v) =>
          l (ev v (locOp v (G.M.co.rho B.ψ (partFin v (shiftA H H' p.2.1))) (locOp v (om (p.1.1, 1)) φ))) *
            (X.ν p.2.1 : ℂ) * ((absE F E p.2.1 : ℝ) : ℂ) ^ ((b + 2 - a') / 2)) (μK.prod μ) := by
  first | exact @GlobalTheory.ConeInteg.integrable_cone_integrand | exact GlobalTheory.ConeInteg.integrable_cone_integrand | (intros; apply GlobalTheory.ConeInteg.integrable_cone_integrand <;> assumption)
