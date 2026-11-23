import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocPart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigBLocalPartStabilizerStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigBLocalPartIntegralStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigBLocalPartIdentityStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.LemF
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.ThK.LemF

theorem coneB_mem_SB : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : Base F E) (a b : ℕ)
    (G : Geo σ a (b + 2)) (G₁ : Geo σ a b) (H : Plane E (b + 2) b) (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' →
    ∀ e', IsEv B G.M' G₁.M' H.ι H'.ι (isoB H H') e' → ∀ ei' ev', IsLocPart G.M' G₁.M' e' ei' ev' →
    ∀ (K : Subgroup (UA σ G.V'.J)), IsStab B K → ∀ X om om' om₁ om₁', IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ (v : Pl F) (μK : Measure (KAt K (evFin F v))) (μ : Measure (idelesAt E (evFin F v))), μK.IsHaarMeasure →
      μ.IsHaarMeasure →
      ∀ φ ∈ SB (Fin (b + 2) × Fin (a + (b + 2)) → Fv F v),
        coneFin B G.M' om' v (ev' v) K μK μ (shiftB σ H H') X.ν ((a - (b + 2)) / 2 + 1) φ ∈ SB (Fin b × Fin (a + b) → Fv F v) := by
  intro hP F E _ _ _ _ _ σ B a b G G₁ H H' cfg e' he' ei' ev' hloc K hK X om om' om₁ om₁' T T₁ v μK μ hμK hμ φ hφ
  obtain ⟨N, f, c, hf, hc1, hc2, hsum⟩ := GlobalTheory.T.config_b_local_part_stabilizer hP F E σ B a b G G₁ H H' cfg e' he' ei' ev' hloc K hK X om om' om₁ om₁'
    T T₁ v μK μ hμK hμ _ (Nat.le_add_left 1 _) φ hφ
  have e : coneFin B G.M' om' v (ev' v) K μK μ (shiftB σ H H') X.ν ((a - (b + 2)) / 2 + 1) φ =
      ∑ i, (∫ k, ∫ l, c i k l ∂μ ∂μK) • f i := by
    funext y
    have h1 : ∀ k : KAt K (evFin F v), ∫ l, coneFinInt B G.M' om' v (ev' v) (shiftB σ H H') X.ν ((a - (b + 2)) / 2 + 1) φ
        k.1 l.1 y ∂μ = ∑ i, (∫ l, c i k l ∂μ) * f i y := fun k => by
      rw [show (fun l : idelesAt E (evFin F v) => coneFinInt B G.M' om' v (ev' v) (shiftB σ H H') X.ν
          ((a - (b + 2)) / 2 + 1) φ k.1 l.1 y) = fun l => ∑ i, c i k l * f i y from funext fun l => hsum k l y]
      rw [integral_finsetSum _ fun j _ => (hc1 j k).mul_const _]
      exact Finset.sum_congr rfl fun j _ => integral_mul_const _ _
    simp only [coneFin, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    simp_rw [h1]
    rw [integral_finsetSum _ fun j _ => (hc2 j).mul_const _]
    exact Finset.sum_congr rfl fun j _ => integral_mul_const _ _
  rw [e]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hf i)

theorem coneLawB : GlobalTheory.FunPr.Hypotheses₂ → ConeLawB := by
  intro hP F E _ _ _ _ _ σ B a b G G₁ H H' cfg e' he' ei' ev' hloc K hK X om om' om₁ om₁' T T₁ v μK μ hμK hμ
  exact ⟨coneB_mem_SB hP F E σ B a b G G₁ H H' cfg e' he' ei' ev' hloc K hK X om om' om₁ om₁' T T₁ v μK μ hμK hμ,
    GlobalTheory.T.config_b_local_part_integral hP F E σ B a b G G₁ H H' cfg e' he' ei' ev' hloc K hK X om om' om₁ om₁' T T₁ v μK μ hμK hμ,
    GlobalTheory.T.config_b_local_part_identity hP F E σ B a b G G₁ H H' cfg e' he' ei' ev' hloc K hK X om om' om₁ om₁' T T₁ v μK μ hμK hμ⟩

end GlobalTheory.ThK.LemF

end
