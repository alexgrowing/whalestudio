import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigBLocalPartStabilizer
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocPart

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.LemF
open GlobalTheory.Doubling (absE)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.config_b_local_part_stabilizer : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : Base F E) (a b : ℕ)
    (G : Geo σ a (b + 2)) (G₁ : Geo σ a b) (H : Plane E (b + 2) b) (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' →
    ∀ e', IsEv B G.M' G₁.M' H.ι H'.ι (isoB H H') e' → ∀ ei' ev', IsLocPart G.M' G₁.M' e' ei' ev' →
    ∀ (K : Subgroup (UA σ G.V'.J)), IsStab B K → ∀ X om om' om₁ om₁', IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ (v : Pl F) (μK : Measure (KAt K (evFin F v))) (μ : Measure (idelesAt E (evFin F v))), μK.IsHaarMeasure →
      μ.IsHaarMeasure → ∀ z : ℕ, 1 ≤ z → ∀ φ ∈ SB (Fin (b + 2) × Fin (a + (b + 2)) → Fv F v),
      ∃ (N : ℕ) (f : Fin N → (Fin b × Fin (a + b) → Fv F v) → ℂ) (c : Fin N → KAt K (evFin F v) → idelesAt E (evFin F v) → ℂ),
        (∀ i, f i ∈ SB (Fin b × Fin (a + b) → Fv F v)) ∧ (∀ i k, Integrable (c i k) μ) ∧
        (∀ i, Integrable (fun k => ∫ l, c i k l ∂μ) μK) ∧
        ∀ k l y, coneFinInt B G.M' om' v (ev' v) (shiftB σ H H') X.ν z φ k.1 l.1 y = ∑ i, c i k l * f i y := by
  first | exact @GlobalTheory.ThK.LemF.coneFinInt_finSum | exact GlobalTheory.ThK.LemF.coneFinInt_finSum | (intros; apply GlobalTheory.ThK.LemF.coneFinInt_finSum <;> assumption)
