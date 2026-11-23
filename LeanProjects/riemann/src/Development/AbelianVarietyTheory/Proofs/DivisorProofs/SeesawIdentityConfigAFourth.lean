import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzValuedIntegralLinear
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ActsInf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSeminormWeylAlg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigATriplesCompatibilityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableIdelesPowerDecay
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigAGoodModelEvaluationSecondStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open Classical

noncomputable section

namespace GlobalTheory.ThK

theorem exists_clm_coneInfFun : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (b a' : ℕ) (G : Geo σ (b + 2) a') (G₁ : Geo σ b a') (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a'))
    (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (om₁ : Rep σ G₁.V G₁.W) (om₁' : Rep σ G₁.V' G₁.W),
    CfgA B G G₁ H H' → IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ e, IsEv B G.M G₁.M H.ι H'.ι (isoA H H') e →
    ∀ (ei : SInf F (Fin (b + 2) × Fin (b + 2 + a')) →L[ℂ] SInf F (Fin b × Fin (b + a')))
      (ev : ∀ v : Pl F, ((Fin (b + 2) × Fin (b + 2 + a') → Fv F v) → ℂ) →ₗ[ℂ] (Fin b × Fin (b + a') → Fv F v) → ℂ),
      ei ≠ 0 → (∀ v, ev v (G.M.vac v) = G₁.M.vac v ∧ (SB _).map (ev v) = SB _) →
      (∀ f φ, (∀ v, φ v ∈ SB _) → (∀ᶠ v in cofinite, φ v = G.M.vac v) → e (pure f φ) = pure (ei f) fun v => ev v (φ v)) →
    ∀ (K : Subgroup (UA σ G.V.J)), IsStab B K → ∀ (μK : Measure (KAt K (evI F))) (μ : Measure (idelesAt E (evI F))),
      IsNormK K (evI F) μK → μ.IsHaarMeasure →
    ∃ T : SInf F (Fin (b + 2) × Fin (b + 2 + a')) →L[ℂ] SInf F (Fin b × Fin (b + a')), ∀ f, ⇑(T f) = coneInfFun B G.M om ei K μK μ (shiftA H H') X.ν ((b + 2 - a') / 2) f := by
  intro hKP F E _ _ _ _ _ σ B b a' G G₁ H H' X om om' om₁ om₁' hC hT hT₁ e he ei ev hei hev hpure K hK μK μ hμK hμ
  obtain ⟨_, _, _, _, _⟩ := idelesAt_facts E (evI F)
  haveI : IsFiniteMeasure μK := ⟨by rw [hμK.2]; exact ENNReal.one_lt_top⟩
  haveI := hμ
  set z := (b + 2 - a') / 2 with hz
  have hz1 : 1 ≤ z := by
    have := hT.geo.eBig
    omega
  have hk : ∀ k ∈ KAt K (evI F), ∀ f : SInf F (Fin (b + 2) × Fin (b + 2 + a')),
      ∃ f₁ : SInf F (Fin (b + 2) × Fin (b + 2 + a')), Acts (evI F) (om (k, 1)) f f₁ :=
    fun k hk' f => GlobalTheory.ThK.ArchActs.acts_inf hKP F E σ B (b + 2) a' G X om om' hT k (mem_KAt.1 hk').2 f
  obtain ⟨N, hN⟩ := GlobalTheory.ArchIdeleDecay.integrable_absE_pow_div F E σ B hT.base μ hμ z hz1
  refine GlobalTheory.ParamSchwartz.iteratedIntegral_clm μK μ (fun f k l => coneInfInt B G.M om ei (shiftA H H') X.ν z f k.1 l.1) ?_ ?_ ?_
  · intro a b' f f' k l
    exact coneInfInt_lin hT.base.std (hk k.1 k.2) a b' f f' l.1
  · intro f n y
    exact GlobalTheory.T.stronglyMeasurable_iteratedFDeriv_coneInfInt_shiftA F E σ hKP.base B b a' G G₁ H H' X om om' hC hT hT₁.geo.hM e he ei ev hei hev hpure K hK z f n y
  · intro a n
    obtain ⟨s, C₄, h4⟩ := GlobalTheory.T.config_a_triples_compatibility hKP F E σ B b a' G G₁ H H' X om om' om₁ om₁' hC hT hT₁ e he ei ev hei hev hpure a n N
    obtain ⟨s', C₃, h3⟩ := GlobalTheory.ArchKX.locOpInf_unif_bound hKP F E σ B (b + 2) a' G X om om' hT K hK s
    refine ⟨s', max C₄ 0 * max C₃ 0, _, hN, fun f k l => ?_⟩
    set q := s.sup (schwartzSeminormFamily ℂ (Fin (b + 2) × Fin (b + 2 + a') → mixedEmbedding.mixedSpace F) ℂ)
    set q' := s'.sup (schwartzSeminormFamily ℂ (Fin (b + 2) × Fin (b + 2 + a') → mixedEmbedding.mixedSpace F) ℂ)
    set P : ℝ := (1 + ∑ w, ‖piInf (B.emb w) (l.1 : AE F E)‖) ^ N with hP
    have hP0 : 0 < P := pow_pos (by positivity) _
    have hA : 0 ≤ (GlobalTheory.Doubling.absE F E l.1 : ℝ) ^ z := by positivity
    have e1 : coneInfInt B G.M om ei (shiftA H H') X.ν z f k.1 l.1 =
        ((X.ν l.1 : ℂ) * ((GlobalTheory.Doubling.absE F E l.1 : ℝ) : ℂ) ^ z) •
          ei (locOpInf (G.M.co.rho B.ψ (partInf F (shiftA H H' l.1))) (locOpInf (om (k.1, 1)) f)) := rfl
    have hn : ‖(X.ν l.1 : ℂ) * ((GlobalTheory.Doubling.absE F E l.1 : ℝ) : ℂ) ^ z‖ = (GlobalTheory.Doubling.absE F E l.1 : ℝ) ^ z := by
      rw [norm_mul, Circle.norm_coe, one_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have h4' := h4 (locOpInf (om (k.1, 1)) f) l.1 l.2
    have h3' := h3 k.1 k.2 f
    have hq0 : 0 ≤ q (locOpInf (om (k.1, 1)) f) := apply_nonneg _ _
    have hq0' : 0 ≤ q' f := apply_nonneg _ _
    set Y := SchwartzMap.seminorm ℂ a n (ei (locOpInf (G.M.co.rho B.ψ (partInf F (shiftA H H' l.1))) (locOpInf (om (k.1, 1)) f)))
    have hY0 : 0 ≤ Y := apply_nonneg _ _
    have hY : Y ≤ max C₄ 0 * (max C₃ 0 * q' f) / P := by
      rw [le_div_iff₀ hP0, mul_comm]
      calc P * Y ≤ C₄ * q (locOpInf (om (k.1, 1)) f) := h4'
        _ ≤ max C₄ 0 * q (locOpInf (om (k.1, 1)) f) := mul_le_mul_of_nonneg_right (le_max_left _ _) hq0
        _ ≤ max C₄ 0 * (max C₃ 0 * q' f) := by
          refine mul_le_mul_of_nonneg_left (h3'.trans ?_) (le_max_right _ _)
          exact mul_le_mul_of_nonneg_right (le_max_left _ _) hq0'
    rw [e1, map_smul_eq_mul, hn]
    calc (GlobalTheory.Doubling.absE F E l.1 : ℝ) ^ z * Y ≤ (GlobalTheory.Doubling.absE F E l.1 : ℝ) ^ z * (max C₄ 0 * (max C₃ 0 * q' f) / P) :=
          mul_le_mul_of_nonneg_left hY hA
      _ = max C₄ 0 * max C₃ 0 * ((GlobalTheory.Doubling.absE F E l.1 : ℝ) ^ z / P) * q' f := by
          field_simp

end GlobalTheory.ThK
