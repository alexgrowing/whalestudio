import Development.WeilBound.ThetaLifts.FrameEstimates.LatSumRedH

noncomputable section

namespace PositivityTheory.ThKEst

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem qht_le {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (g : UA σ J) {γ : UA σ J} (hγ : γ ∈ ratU σ J) : qht g ≤ ht (γ * g) :=
  ciInf_le (OrderBot.bddBelow _) (⟨γ, hγ⟩ : ratU σ J)

theorem psum_self {r : ℕ} (t : Fin r → ℝ) : psum t r = ∑ i, t i :=
  Finset.sum_congr rfl fun j _ => if_pos j.2

theorem psum_le {r : ℕ} {t : Fin r → ℝ} (h : t ∈ Cone r) (i : ℕ) : psum t i ≤ ∑ j, t j :=
  Finset.sum_le_sum fun j _ => by split_ifs; exacts [le_rfl, h.2 j]

theorem soSemiU_of (hT : GrpTop) (hE : EpsOf) (hS : SiegelAll) (hQ : SqSo) (hI : LatInv) (hK : LatCpt) (hL : LatFull)
    (hP : PosWt) : SoSemiU := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hp N₀
  have hc := hp.base.cm
  obtain ⟨hJ, -, -⟩ := hE F E σ B hp.base n X r s (Or.inl hp.herm)
  obtain ⟨hJ', -, -⟩ := hE F E σ B hp.base d W r' s' (Or.inr hp.skew)
  obtain ⟨fr, hg, -, ⟨Ω, hΩ, hcov⟩, -, ⟨C₀, k₀, hht⟩⟩ := hS F E σ hc n X.J hJ
  obtain ⟨fr', hg', -, ⟨Ω', hΩ', hcov'⟩, -, hht'⟩ := hS F E σ hc d W.J hJ'
  obtain ⟨A, k₁, hA0, hAk⟩ := exp_le_ht hT hc hJ' hht' hΩ'
  obtain ⟨B₀, hB₀⟩ := (hT F E σ hc n X.J hJ).2.2.2.2.2.2.2 Ω hΩ
  set D : ℕ := Module.finrank ℚ E with hD
  set m : ℕ := D * d + 2 * (k₀ * N₀) with hm
  obtain ⟨N, hN⟩ := hL F E σ hc B.emb n d X.J W.J hJ hJ' fr fr' hg hg' m
  refine ⟨k₁ * (m + D * n), fun φ hφ => ?_⟩
  obtain ⟨p, C, hpc, hC, hb⟩ := hQ F E σ B n d X W M χX χW om r s r' s' hp φ hφ N
  obtain ⟨C₁, K₁, hC₁, h₁⟩ := hK F E σ hc B.emb n d X.J W.J hJ hJ' Ω Ω' hΩ hΩ' C N hC
  obtain ⟨K₂, h₂⟩ := hN C₁ hC₁
  set K : ℝ := (K₁ * K₂ + 1) * (max C₀ 0 * B₀) ^ N₀ * A ^ (m + D * n) with hKdef
  have hK0 : 0 ≤ K := by positivity
  refine ⟨NNReal.mk K hK0 • p, (continuous_const.mul hpc : Continuous fun f => K * p f), fun f g h => ?_⟩
  obtain ⟨γ, hγ, s₁, hs, κ, hκ, e⟩ := hcov g
  obtain ⟨δ, hδ, t, ht', κ', hκ', e'⟩ := hcov' h
  have hpf : 0 ≤ p f := apply_nonneg p f
  obtain ⟨hw, hv0, hv⟩ := hP n d fr.r fr'.r s₁ t hs ht'
  set S := ∑ i, s₁ i with hSdef
  set T := ∑ j, t j with hTdef
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun i _ => hs.2 i
  have hT0 : 0 ≤ T := Finset.sum_nonneg fun i _ => ht'.2 i
  have hST : S ≤ T + viol s₁ t := by
    have := hv fr.r le_rfl
    rw [psum_self] at this
    linarith [psum_le ht' fr.r]
  have e1 := hb f g h
  rw [← hI F E σ hc B.emb n d X.J W.J hJ hJ' C N (fullRank E n d) (by simp) γ hγ δ hδ g h, e, e'] at e1
  have e2 := e1.trans (mul_le_mul_right ((h₁ _ _ _ κ hκ κ' hκ').trans (mul_le_mul_right (h₂ s₁ hs t ht') _)) _)
  set x : ℝ := D * posWt n d s₁ t - m * viol s₁ t with hx
  have e3 : ‖theta om (pureA F f φ) g h‖ ^ 2 ≤ p f ^ 2 * (K₁ * (K₂ * Real.exp x)) := by
    rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _), ← ENNReal.ofReal_pow hpf, ← ENNReal.ofReal_coe_nnreal,
      ← ENNReal.ofReal_coe_nnreal (p := K₂), ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul (by positivity)] at e2
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 e2
  have e4 : ‖theta om (pureA F f φ) g h‖ ≤ p f * ((K₁ * K₂ + 1) * Real.exp (x / 2)) := by
    refine (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 ?_
    refine e3.trans ?_
    have h5 : Real.exp (x / 2) ^ 2 = Real.exp x := by rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    have h6 : (0 : ℝ) ≤ K₁ * K₂ := by positivity
    rw [mul_pow, mul_pow, h5, ← mul_assoc (K₁ : ℝ)]
    gcongr
    nlinarith
  have e5 : (qht g : ℝ) ≤ max C₀ 0 * B₀ * Real.exp (k₀ * S) := by
    have a1 : (qht g : ℝ) ≤ ht (fr.a s₁) * B₀ := by
      have := (qht_le g hγ).trans (e ▸ (ht_mul_le _ _).trans (mul_le_mul_right (hB₀ κ hκ) _))
      exact_mod_cast this
    have a2 : (ht (fr.a s₁) : ℝ) ≤ max C₀ 0 * Real.exp (k₀ * S) :=
      (hht s₁ hs).1.trans (by gcongr; exact le_max_left _ _)
    calc _ ≤ _ := a1
      _ ≤ max C₀ 0 * Real.exp (k₀ * S) * B₀ := by gcongr
      _ = _ := by ring
  have e6 : x / 2 + N₀ * (k₀ * S) ≤ ((m + D * n : ℕ) : ℝ) * T := by
    have hD0 : (0 : ℝ) ≤ D := Nat.cast_nonneg _
    have b1 : (D : ℝ) * posWt n d s₁ t ≤ D * (d * S + n * T) := mul_le_mul_of_nonneg_left hw hD0
    have hmr : (m : ℝ) = D * d + 2 * (k₀ * N₀) := by rw [hm]; push_cast; ring
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
    have b2 : (m : ℝ) * S ≤ m * (T + viol s₁ t) := mul_le_mul_of_nonneg_left hST hm0
    have b3 : (0 : ℝ) ≤ m * T := mul_nonneg hm0 hT0
    have b4 : (0 : ℝ) ≤ D * n * T := by positivity
    have b5 : (m : ℝ) * S = D * d * S + 2 * (N₀ * (k₀ * S)) := by rw [hmr]; ring
    rw [hx]
    push_cast
    nlinarith
  have e7 : Real.exp (((m + D * n : ℕ) : ℝ) * T) ≤ A ^ (m + D * n) * (ht h : ℝ) ^ (k₁ * (m + D * n)) := by
    rw [Real.exp_nat_mul, pow_mul, ← mul_pow]
    exact pow_le_pow_left₀ (Real.exp_pos _).le (hAk h δ hδ t ht' κ' hκ' e') _
  calc ‖theta om (pureA F f φ) g h‖ * (qht g : ℝ) ^ N₀
      ≤ p f * ((K₁ * K₂ + 1) * Real.exp (x / 2)) * (max C₀ 0 * B₀ * Real.exp (k₀ * S)) ^ N₀ := by gcongr
    _ = p f * ((K₁ * K₂ + 1) * (max C₀ 0 * B₀) ^ N₀) * Real.exp (x / 2 + N₀ * (k₀ * S)) := by
        rw [Real.exp_add, mul_pow _ (Real.exp _), ← Real.exp_nat_mul]; ring
    _ ≤ p f * ((K₁ * K₂ + 1) * (max C₀ 0 * B₀) ^ N₀) * (A ^ (m + D * n) * (ht h : ℝ) ^ (k₁ * (m + D * n))) := by
        gcongr
        exact (Real.exp_le_exp.2 e6).trans e7
    _ = (K * p f) * (ht h : ℝ) ^ (k₁ * (m + D * n)) := by rw [hKdef]; ring

theorem domSoU_of (hE : EpsOf) (hV : FinVolU) (hS : SoSemiU) : DomSoU := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hp
  obtain ⟨hJ, -, -⟩ := hE F E σ B hp.base n X r s (Or.inl hp.herm)
  obtain ⟨k, hk⟩ := hS F E σ B n d X W M χX χW om r s r' s' hp 0
  refine ⟨k, fun φ hφ => ?_⟩
  obtain ⟨p, hpc, hb⟩ := hk φ hφ
  refine ⟨p, fun _ => 1, hpc, measurable_const, ?_, fun f g h => ?_⟩
  · rw [setLIntegral_one]
    exact hV F E σ hp.base.cm n X.J hJ M.μ M.dom hp.good.haar hp.good.dom
  · rw [mul_one, ← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (by simpa using hb f g h)

end PositivityTheory.ThKEst

end
