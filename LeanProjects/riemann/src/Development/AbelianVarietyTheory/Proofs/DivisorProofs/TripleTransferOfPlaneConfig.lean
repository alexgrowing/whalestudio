import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzValuedDoubleIntegralStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousKernelIntegralProdStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigAThetaIntegralUnfoldStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigAThetaIntegralFoldStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigAThetaIntegralCompareStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigAThetaIntegralEqualStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open Classical

noncomputable section

namespace GlobalTheory.ThK

theorem re_conj_mul_pos_of_near {c w : ℂ} (hc : 0 < ‖c‖) (h : ‖w - c‖ < ‖c‖ / 2) : 0 < (starRingEnd ℂ c * w).re := by
  have hcc : (starRingEnd ℂ c * c).re = ‖c‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; first | (simp [Complex.mul_re]; done) | (simp [Complex.mul_re]; ring)
  have h1 : (starRingEnd ℂ c * w).re = ‖c‖ ^ 2 + (starRingEnd ℂ c * (w - c)).re := by
    rw [mul_sub, Complex.sub_re, hcc]; ring
  have h2 : |(starRingEnd ℂ c * (w - c)).re| ≤ ‖c‖ * ‖w - c‖ := by
    calc _ ≤ ‖starRingEnd ℂ c * (w - c)‖ := Complex.abs_re_le_norm _
      _ = ‖c‖ * ‖w - c‖ := by rw [norm_mul, Complex.norm_conj]
  have h3 : ‖c‖ * ‖w - c‖ ≤ ‖c‖ * (‖c‖ / 2) := mul_le_mul_of_nonneg_left h.le hc.le
  rw [h1]
  nlinarith [neg_abs_le (starRingEnd ℂ c * (w - c)).re]

theorem coneInf_bump_ne_zero : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
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
    ∀ l : SInf F (Fin b × Fin (b + a')) →L[ℂ] ℂ, l ≠ 0 →
      (∀ g ∈ UAt σ G₁.V (evI F), ∀ f f₁ : SInf F (Fin b × Fin (b + a')), Acts (evI F) (om₁ (g, 1)) f f₁ → l f₁ = l f) →
    ∀ T : SInf F (Fin (b + 2) × Fin (b + 2 + a')) →L[ℂ] SInf F (Fin b × Fin (b + a')), (∀ f, ⇑(T f) = coneInfFun B G.M om ei K μK μ (shiftA H H') X.ν ((b + 2 - a') / 2) f) →
      ∃ f : SInf F (Fin (b + 2) × Fin (b + 2 + a')), l (T f) ≠ 0 := by
  intro hKP F E _ _ _ _ _ σ B b a' G G₁ H H' X om om' om₁ om₁' hCfg hT hT₁ e he ei ev hei hev hpure K hK μK μ hμK hμ l hl
    hinv T hTf
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsTopologicalRing (AE F E) := GlobalTheory.Doubling.isTopologicalRing_tens
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  obtain ⟨eh⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (AF F)
  haveI : SecondCountableTopology (AE F E) := eh.secondCountableTopology
  haveI : SecondCountableTopology (Matrix (Fin (b + 2)) (Fin (b + 2)) (AE F E)) :=
    inferInstanceAs (SecondCountableTopology (Fin (b + 2) → Fin (b + 2) → AE F E))
  haveI : SecondCountableTopology (Matrix (Fin (b + 2)) (Fin (b + 2)) (AE F E))ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  haveI : SecondCountableTopology (Matrix (Fin (b + 2)) (Fin (b + 2)) (AE F E))ˣ :=
    Units.isEmbedding_embedProduct.secondCountableTopology
  haveI : BorelSpace (UA σ G.V.J) := ⟨rfl⟩
  obtain ⟨_, _, _, _, _⟩ := idelesAt_facts E (evI F)
  haveI := hμK.1
  haveI hfin : IsFiniteMeasure μK := ⟨by rw [hμK.2]; exact ENNReal.one_lt_top⟩
  haveI : SFinite μK := @MeasureTheory.instSFiniteOfSigmaFinite _ _ μK (@MeasureTheory.IsFiniteMeasure.toSigmaFinite _ _ μK hfin)
  set z := (b + 2 - a') / 2
  obtain ⟨f₀, hc⟩ := GlobalTheory.T.config_A_theta_integral_compare hKP F E σ B b a' G G₁ H H' X om om' om₁ om₁' hCfg hT hT₁ e he ei ev hei hev hpure K hK μK μ hμK hμ l hl hinv
  set c := l (coneInfInt B G.M om ei (shiftA H H') X.ν z f₀ 1 1) with hcdef
  have hG : Continuous fun p : KAt K (evI F) × idelesAt E (evI F) => l (coneInfInt B G.M om ei (shiftA H H') X.ν z f₀ p.1.1 p.2.1) :=
    l.continuous.comp (GlobalTheory.T.config_A_theta_integral_unfold hKP F E σ B b a' G G₁ H H' X om om' om₁ om₁' hCfg hT hT₁ e he ei ev hei hev hpure K hK μK μ hμK hμ l hl hinv f₀)
  set O : Set (KAt K (evI F) × idelesAt E (evI F)) :=
    {p | ‖l (coneInfInt B G.M om ei (shiftA H H') X.ν z f₀ p.1.1 p.2.1) - c‖ < ‖c‖ / 2} with hOdef
  have hO : IsOpen O := isOpen_lt (continuous_norm.comp (hG.sub continuous_const)) continuous_const
  have hc0 : 0 < ‖c‖ := norm_pos_iff.2 hc
  have hSig : ∀ (k : KAt K (evI F)) (t : idelesAt E (evI F)),
      mat k.1⁻¹ *ᵥ ((t.1 : AE F E) • incV F H.x) = incV F H.x → (k, t) ∈ O := fun k t h => by
    show ‖_ - c‖ < ‖c‖ / 2
    rw [GlobalTheory.T.config_A_theta_integral_fold hKP F E σ B b a' G G₁ H H' X om om' om₁ om₁' hCfg hT hT₁ e he ei ev hei hev hpure K hK μK μ hμK hμ l hl hinv f₀ k t h,
      ← hcdef, sub_self, norm_zero]
    exact half_pos hc0
  obtain ⟨f, Ψ, C, hΨ, hΨ0, hΨ1, hCc, hCO, hΨC, hf⟩ :=
    GlobalTheory.T.config_A_theta_integral_equal hKP F E σ B b a' G G₁ H H' X om om' om₁ om₁' hCfg hT hT₁ e he ei ev hei hev hpure K hK μK μ hμK hμ l hl hinv f₀ O hO hSig
  refine ⟨f, ?_⟩
  have hcont : Continuous fun p : KAt K (evI F) × idelesAt E (evI F) => coneInfInt B G.M om ei (shiftA H H') X.ν z f p.1.1 p.2.1 := by
    have e1 : (fun p : KAt K (evI F) × idelesAt E (evI F) => coneInfInt B G.M om ei (shiftA H H') X.ν z f p.1.1 p.2.1) =
        fun p => (Ψ p : ℂ) • coneInfInt B G.M om ei (shiftA H H') X.ν z f₀ p.1.1 p.2.1 := funext hf
    rw [e1]
    exact (Complex.continuous_ofReal.comp hΨ).smul
      (GlobalTheory.T.config_A_theta_integral_unfold hKP F E σ B b a' G G₁ H H' X om om' om₁ om₁' hCfg hT hT₁ e he ei ev hei hev hpure K hK μK μ hμK hμ l hl hinv f₀)
  have hzero : ∀ p ∉ C, coneInfInt B G.M om ei (shiftA H H') X.ν z f p.1.1 p.2.1 = 0 := fun p hp => by
    rw [hf p, hΨC p hp, Complex.ofReal_zero, zero_smul]
  have hlT : l (T f) = ∫ k, ∫ t, l (coneInfInt B G.M om ei (shiftA H H') X.ν z f k.1 t.1) ∂μ ∂μK :=
    GlobalTheory.T.schwartz_valued_double_integral μK μ (fun k t => coneInfInt B G.M om ei (shiftA H H') X.ν z f k.1 t.1) hcont C hCc hzero (T f)
      (fun y => by rw [hTf]; rfl) l
  rw [hlT]
  refine GlobalTheory.T.continuous_kernel_integral_prod μK μ (fun k t => l (coneInfInt B G.M om ei (shiftA H H') X.ν z f k.1 t.1))
    (l.continuous.comp hcont) C hCc (fun p hp => by simp only [hzero p hp, map_zero]) c (fun k t => ?_) 1 1 ?_
  · rw [hf (k, t), map_smul, smul_eq_mul, mul_left_comm, Complex.re_ofReal_mul]
    by_cases h0 : Ψ (k, t) = 0
    · simp [h0]
    · have hm : (k, t) ∈ O := hCO (by_contra fun h => h0 (hΨC _ h))
      exact mul_nonneg (hΨ0 _) (re_conj_mul_pos_of_near hc0 hm).le
  · rw [hf (1, 1), map_smul, smul_eq_mul, mul_left_comm, Complex.re_ofReal_mul]
    have hm : ((1 : KAt K (evI F)), (1 : idelesAt E (evI F))) ∈ O := hSig 1 1 (by simp [mat])
    exact mul_pos hΨ1 (re_conj_mul_pos_of_near hc0 hm)

end GlobalTheory.ThK

end
