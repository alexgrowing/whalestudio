import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFinsetOfEventually
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LintegralFintypeProdEqProd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdemSmulUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DOpMemDStep
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ActsDIffDOp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilActionMapsSchwartz
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzValuedIntegralLinearStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableIdelesPowerDecayStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TripleSchwartzSeminormBoundStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigAGoodModelEvaluationFirstStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigAGoodModelEvaluationSecondStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KInfinityPreservesPolynomialDegreeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigAGoodModelEvaluationThirdStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralSchwartzFamilyMemSpaceStatement
open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.ConeEuler
open GlobalTheory.Doubling (absE absEv unitFin ideleAt)
open Classical

noncomputable section

namespace GlobalTheory.ThK.ConeEuler

theorem coneInf_schwartz_pol : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), GlobalTheory.FunPr.Hypotheses₂ → ∀ (B : Base F E) (b a' : ℕ) (G : Geo σ (b + 2) a') (G₁ : Geo σ b a') (H : Plane E (b + 2) b)
    (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' →
    ∀ (e : Fn F (b + 2) (b + 2 + a') →ₗ[ℂ] Fn F b (b + a')), IsEv B G.M G₁.M H.ι H'.ι (isoA H H') e →
    ∀ (ei : SInf F (Fin (b + 2) × Fin (b + 2 + a')) →L[ℂ] SInf F (Fin b × Fin (b + a')))
      (ev : ∀ v : Pl F, ((Fin (b + 2) × Fin (b + 2 + a') → Fv F v) → ℂ) →ₗ[ℂ] (Fin b × Fin (b + a') → Fv F v) → ℂ),
    (ei ≠ 0 ∧ (∀ v, ev v (G.M.vac v) = G₁.M.vac v ∧ (SB _).map (ev v) = SB _) ∧
      ∀ f φ, (∀ v, φ v ∈ SB _) → (∀ᶠ v in cofinite, φ v = G.M.vac v) → e (pure f φ) = pure (ei f) fun v => ev v (φ v)) →
    ∀ (K : Subgroup (UA σ G.V.J)), IsStab B K →
    ∀ (μKv : ∀ v : Pl F, Measure (KAt K (evFin F v))), (∀ v, IsNormK K (evFin F v) (μKv v)) →
    ∀ (μEv : ∀ v : Pl F, Measure (idelesAt E (evFin F v))), (∀ v, IsNormE E v (μEv v)) →
    ∀ (μKi : Measure (KAt K (evI F))), IsNormK K (evI F) μKi → ∀ (μEi : Measure (idelesAt E (evI F))), μEi.IsHaarMeasure →
    ∀ (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' → G₁.M.IsGood B.ψ →
    ∀ f : SInf F (Fin (b + 2) × Fin (b + 2 + a')), ∃ g : SInf F (Fin b × Fin (b + a')),
      ⇑g = coneInfFun B G.M om ei K μKi μEi (shiftA H H') X.ν ((b + 2 - a') / 2) f ∧
      (f ∈ G.M.Pol B.ψ B.emb → g ∈ G₁.M.Pol B.ψ B.emb) := by
  intro F E _ _ _ _ _ σ hPr B b a' G G₁ H H' hC e he ei ev hev0 K hK μKv _ μEv _ μKi hμK μEi hμ X om om' hT hG₁ f
  obtain ⟨hei, hev, hpure⟩ := hev0
  obtain ⟨_, _, _, _, _⟩ := idelesAt_facts E (evI F)
  haveI : IsFiniteMeasure μKi := ⟨by rw [hμK.2]; exact ENNReal.one_lt_top⟩
  haveI := hμ
  set z := (b + 2 - a') / 2 with hz
  have hz1 : 1 ≤ z := by
    have := hT.geo.eBig
    omega
  have hk : ∀ k ∈ KAt K (evI F), ∀ f : SInf F (Fin (b + 2) × Fin (b + 2 + a')),
      ∃ f₁ : SInf F (Fin (b + 2) × Fin (b + 2 + a')), Acts (evI F) (om (k, 1)) f f₁ :=
    fun k hk' f => GlobalTheory.ArchLocalityX.acts_arch_left hPr F E σ (b + 2) (b + 2 + a') G.V G.W G.M B.ψ X.β (X.β / X.α) om
      hT.base.cm hT.base.std hT.weil k (mem_KAt.1 hk').2 f
  obtain ⟨N, hN⟩ := GlobalTheory.T.integrable_ideles_power_decay F E σ B hT.base μEi hμ z hz1
  have hbd : ∀ a n : ℕ, ∃ (s : Finset (ℕ × ℕ)) (C : ℝ) (w : idelesAt E (evI F) → ℝ), Integrable w μEi ∧
      ∀ f (k : KAt K (evI F)) (l : idelesAt E (evI F)),
        SchwartzMap.seminorm ℂ a n (coneInfInt B G.M om ei (shiftA H H') X.ν z f k.1 l.1) ≤
          C * w l * (s.sup (schwartzSeminormFamily ℂ (Fin (b + 2) × Fin (b + 2 + a') → mixedEmbedding.mixedSpace F) ℂ)) f := by
    intro a n
    obtain ⟨s, C₄, h4⟩ := GlobalTheory.T.config_a_good_model_evaluation_first F E σ hPr B b a' G G₁ H H' X om om' hC hT hG₁ e he ei ev hei hev hpure a n N
    obtain ⟨s', C₃, h3⟩ := GlobalTheory.T.triple_schwartz_seminorm_bound F E σ hPr B (b + 2) a' G X om om' hT K hK s
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
  have hmeas : ∀ f (n : ℕ) (y : Fin b × Fin (b + a') → mixedEmbedding.mixedSpace F),
      StronglyMeasurable (Function.uncurry fun (k : KAt K (evI F)) (l : idelesAt E (evI F)) =>
        iteratedFDeriv ℝ n (⇑(coneInfInt B G.M om ei (shiftA H H') X.ν z f k.1 l.1)) y) :=
    fun f n y => GlobalTheory.T.stronglyMeasurable_iteratedFDeriv_coneInfInt_shiftA F E σ hPr B b a' G G₁ H H' X om om' hC hT hG₁ e he ei ev hei hev hpure K hK z f n y
  obtain ⟨Tc, hTc⟩ := GlobalTheory.T.schwartz_valued_integral_linear μKi μEi (fun f (k : KAt K (evI F)) (l : idelesAt E (evI F)) =>
      coneInfInt B G.M om ei (shiftA H H') X.ν z f k.1 l.1)
    (fun a b' f f' k l => coneInfInt_lin hT.base.std (hk k.1 k.2) a b' f f' l.1) hmeas hbd
  refine ⟨Tc f, hTc f, fun hf => ?_⟩
  have hψ : IsStd B.ψ := hT.base.std
  have hdir : Directed (· ≤ ·) (GlobalTheory.FockKFin.polLe G.M B.emb) := (GlobalTheory.FockKFin.polLe_mono G.M B.emb).directed_le
  have hsub : G.M.Pol B.ψ B.emb ≤ ⨆ m, GlobalTheory.FockKFin.polLe G.M B.emb m := by
    rw [GlobalTheory.ThK.EvAt0.PolEv.pol_eq hψ]
    refine sInf_le ⟨fun g hg => Submodule.mem_iSup_of_mem 0 (Submodule.subset_span hg), fun a b g hg => ?_⟩
    obtain ⟨m, hm⟩ := (Submodule.mem_iSup_of_directed _ hdir).1 hg
    refine Submodule.mem_iSup_of_mem (m + 1) ?_
    rw [GlobalTheory.FockKFin.polLe_succ]
    exact Submodule.mem_sup_right (GlobalTheory.FockKFin.dOp_mem_dStep _ a b hm)
  obtain ⟨m, hm⟩ := (Submodule.mem_iSup_of_directed _ hdir).1 (hsub hf)
  obtain ⟨V, hVfin, hVle, hV⟩ := GlobalTheory.T.config_a_good_model_evaluation_third F E σ hPr B b a' G G₁ H H' X om om' hC hT hG₁ e he ei ev hei hev hpure m
  have hmem : ∀ (k : KAt K (evI F)) (l : idelesAt E (evI F)), coneInfInt B G.M om ei (shiftA H H') X.ν z f k.1 l.1 ∈ V :=
    fun k l => V.smul_mem _ (hV l.1 l.2 _
      (GlobalTheory.T.k_infinity_preserves_polynomial_degree F E σ hPr B (b + 2) a' G X om om' hT k.1 ((mem_KAt_inf hK).1 k.2) m f hm))
  obtain ⟨s, C, w, hw, hb⟩ := hbd 0 0
  obtain ⟨g', hg'V, hg'⟩ := GlobalTheory.T.integral_schwartz_family_mem_space μKi μEi V hVfin
    (fun (k : KAt K (evI F)) (l : idelesAt E (evI F)) => coneInfInt B G.M om ei (shiftA H H') X.ν z f k.1 l.1) hmem
    (fun y => hmeas f 0 y)
    ⟨C * (s.sup (schwartzSeminormFamily ℂ (Fin (b + 2) × Fin (b + 2 + a') → mixedEmbedding.mixedSpace F) ℂ)) f, w, hw,
      fun k l => (hb f k l).trans (le_of_eq (by ring))⟩
  have e2 : Tc f = g' := DFunLike.coe_injective ((hTc f).trans hg'.symm)
  rw [e2]
  exact hVle hg'V

end GlobalTheory.ThK.ConeEuler

end
