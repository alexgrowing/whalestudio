import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalPartEvalStabilizer
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocPart
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_part_eval_stabilizer : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (b a' : ℕ)
    (G : Geo σ (b + 2) a') (G₁ : Geo σ b a') (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' →
    ∀ e, IsEv B G.M G₁.M H.ι H'.ι (isoA H H') e → ∀ ei ev, GlobalTheory.ThK.LemF.IsLocPart G.M G₁.M e ei ev →
    ∀ (K : Subgroup (UA σ G.V.J)), IsStab B K → ∀ X om om' om₁ om₁', IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ (v : Pl F) (μK : Measure (KAt K (evFin F v))) (μ : Measure (idelesAt E (evFin F v))), μK.IsHaarMeasure →
      μ.IsHaarMeasure → ∀ φ ∈ SB (Fin (b + 2) × Fin (b + 2 + a') → Fv F v),
      ∃ (N : ℕ) (g : Fin N → (Fin b × Fin (b + a') → Fv F v) → ℂ) (c : Fin N → ℂ), (∀ i, g i ∈ SB (Fin b × Fin (b + a') → Fv F v)) ∧
        ∀ (L : ((Fin b × Fin (b + a') → Fv F v) → ℂ) →ₗ[ℂ] ((Fin b × Fin (b + a') → Fv F v) → ℂ)) (y : Fin b × Fin (b + a') → Fv F v),
          ∫ k, ∫ l, L (ev v (locOp v (G.M.co.rho B.ψ (partFin v (shiftA H H' l.1))) (locOp v (om (k.1, 1)) φ))) y *
            (X.ν l.1 : ℂ) * ((absE F E l.1 : ℝ) : ℂ) ^ ((b + 2 - a') / 2) ∂μ ∂μK = ∑ i, c i * L (g i) y := by
  first | exact @GlobalTheory.ThK.LemF.coneFin_finite_comb | exact GlobalTheory.ThK.LemF.coneFin_finite_comb | (intros; apply GlobalTheory.ThK.LemF.coneFin_finite_comb <;> assumption)
