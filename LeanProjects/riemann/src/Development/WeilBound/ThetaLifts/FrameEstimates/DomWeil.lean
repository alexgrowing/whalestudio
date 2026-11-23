import Development.WeilBound.ThetaLifts.FrameEstimates.LatSumRedH

noncomputable section

namespace PositivityTheory.ThKEst

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem domWeilU_of (hT : GrpTop) (hE : EpsOf) (hS : SiegelAll) (hQ : SqAll) (hI : LatInv) (hM : LatMeas) (hK : LatCpt)
    (hA : LatArch) (hL : LatTor) (hP : PosWt) (h2 : ConeIntegralsFinite) : DomWeilU := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hp hw
  have hc := hp.base.cm
  obtain ⟨hJ, -, hr⟩ := hE F E σ B hp.base n X r s (Or.inl hp.herm)
  obtain ⟨hJ', -, -⟩ := hE F E σ B hp.base d W r' s' (Or.inr hp.skew)
  obtain ⟨fr, hg, -, -, hint, -⟩ := hS F E σ hc n X.J hJ
  obtain ⟨fr', hg', -, -, -, -⟩ := hS F E σ hc d W.J hJ'
  obtain ⟨N, hN⟩ := hL F E σ hc B.emb n d X.J W.J hJ hJ' fr fr' hg hg'
  obtain ⟨k, hk⟩ := latSum_redH hT hS hI hK hA hc B.emb hJ hJ' N
  refine ⟨k, fun φ hφ => ?_⟩
  obtain ⟨p, C, hpc, hC, hb⟩ := hQ F E σ B n d X W M χX χW om r s r' s' hp φ hφ N
  obtain ⟨C', K, hC', hK0, hb'⟩ := hk C hC
  obtain ⟨K₀, Ω, hK₀, hΩ, hi⟩ := hint M.μ M.dom hp.good.haar hp.good.dom
  obtain ⟨C₁, K₁, hC₁, h₁⟩ := hK F E σ hc B.emb n d X.J W.J hJ hJ' Ω {1} hΩ isCompact_singleton C' N hC'
  obtain ⟨K₂, h₂'⟩ := hN C₁ hC₁
  have ha0 : fr'.a 0 = 1 := by
    have := hg'.add 0 0
    rw [add_zero] at this
    exact left_eq_mul.1 this
  have h0 : (0 : Fin fr'.r → ℝ) ∈ Cone fr'.r := ⟨fun _ _ _ => le_rfl, fun _ => le_rfl⟩
  have hmeas : Measurable fun g : UA σ X.J => latSum B.emb C' N Set.univ g (1 : UA σ W.J) ^ (1 / 2 : ℝ) :=
    (hM F E σ hc B.emb n d X.J W.J hJ hJ' C' N Set.univ hC' 1).pow_const _
  set D : ℝ := (Module.finrank ℚ E : ℝ) with hD
  have hD0 : 0 < D := by
    rw [hD]; exact_mod_cast Module.finrank_pos
  refine ⟨NNReal.mk K hK0 • p, fun g => latSum B.emb C' N Set.univ g (1 : UA σ W.J) ^ (1 / 2 : ℝ), ?_, hmeas, ?_, ?_⟩
  · exact (continuous_const.mul hpc : Continuous fun f => K * p f)
  · have hq : fr.r = 0 ∨ d + 2 * fr.r < 2 * n := by
      have := hr fr hg
      omega
    have hfin := (h2 n d fr.r 0 D hD0 hq (Or.inl rfl)).1
    set c : ℝ≥0∞ := ((K₁ : ℝ≥0∞) * K₂) ^ (1 / 2 : ℝ) with hcdef
    have hcfin : c < ⊤ := ENNReal.rpow_lt_top_of_nonneg (by norm_num) (ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.coe_ne_top)
    have key := hi (fun t => c * ENNReal.ofReal (Real.exp (D * (d / 2 * ∑ i, t i)))) (by fun_prop) _ hmeas
      (fun γ hγ g => by
        have := hI F E σ hc B.emb n d X.J W.J hJ hJ' C' N Set.univ (by simp) γ hγ 1 (one_mem _) g 1
        rw [mul_one] at this
        rw [this])
      (fun t ht' κ hκ => by
        have e1 := h₁ Set.univ (fr.a t) 1 κ hκ 1 rfl
        rw [mul_one] at e1
        have e2 := h₂' t ht' 0 h0
        rw [ha0] at e2
        have e3 : posWt n d t (0 : Fin fr'.r → ℝ) ≤ d * ∑ i, t i := by
          simpa using (hP n d fr.r fr'.r t 0 ht' h0).1
        have e4 : latSum B.emb C' N Set.univ (fr.a t * κ) (1 : UA σ W.J) ≤
            ((K₁ : ℝ≥0∞) * K₂) * ENNReal.ofReal (Real.exp (D * (d / 2 * ∑ i, t i))) ^ (2 : ℝ) := by
          refine e1.trans ?_
          rw [mul_assoc]
          refine mul_le_mul_right (e2.trans (mul_le_mul_right ?_ _)) _
          rw [ENNReal.ofReal_rpow_of_pos (Real.exp_pos _), ← Real.exp_mul]
          refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
          nlinarith
        refine (ENNReal.rpow_le_rpow e4 (by norm_num)).trans (le_of_eq ?_)
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← ENNReal.rpow_mul]
        norm_num [hcdef])
    refine key.trans_lt (ENNReal.mul_lt_top hK₀ ?_)
    simp only [mul_assoc c]
    rw [lintegral_const_mul' _ _ hcfin.ne]
    exact ENNReal.mul_lt_top hcfin hfin
  · intro f g h
    have e := (hb f g h).trans (mul_le_mul_right (hb' g h) _)
    have hpf : 0 ≤ p f := apply_nonneg p f
    have e2 : ‖theta om (pureA F f φ) g h‖ₑ ^ (2 : ℝ) ≤
        ENNReal.ofReal (K * p f * (ht h : ℝ) ^ k) ^ (2 : ℝ) * latSum B.emb C' N Set.univ g (1 : UA σ W.J) := by
      rw [ENNReal.rpow_two, ENNReal.rpow_two]
      refine e.trans (le_of_eq ?_)
      rw [← mul_assoc, ← ENNReal.ofReal_pow hpf, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_pow (by positivity)]
      congr 2
      ring
    have e3 := ENNReal.rpow_le_rpow e2 (show (0 : ℝ) ≤ 1 / 2 by norm_num)
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← ENNReal.rpow_mul, ← ENNReal.rpow_mul] at e3
    norm_num at e3
    simpa [NNReal.smul_def] using e3

end PositivityTheory.ThKEst

end
