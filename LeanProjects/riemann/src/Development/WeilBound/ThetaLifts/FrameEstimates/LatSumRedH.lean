import Development.WeilBound.ThetaLifts.FrameEstimates.HodgeTateFromSandwich

noncomputable section

namespace PositivityTheory.ThKEst

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem ht_mul_le {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (g h : UA σ J) : ht (g * h) ≤ ht g * ht h :=
  heightGL_mul_le F g.1 h.1

theorem ht_inv {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (g : UA σ J) : ht g⁻¹ = ht g := heightGL_inv F g.1

theorem one_le_ht {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (g : UA σ J) : 1 ≤ ht g := one_le_heightGL F g.1

theorem exp_le_ht (hT : GrpTop) (hc : IsCMExt F E σ) {d : ℕ} {J : Matrix (Fin d) (Fin d) E} (hJ : EpsHerm σ J)
    {fr : Frame σ J} (h2 : TorHt fr) {Ω : Set (UA σ J)} (hΩ : IsCompact Ω) :
    ∃ (A : ℝ) (k : ℕ), 0 ≤ A ∧ ∀ h : UA σ J, ∀ δ ∈ ratU σ J, ∀ t ∈ Cone fr.r, ∀ κ ∈ Ω, δ * h = fr.a t * κ →
      Real.exp (∑ i, t i) ≤ A * (ht h : ℝ) ^ k := by
  obtain ⟨C, k, hC⟩ := h2
  obtain ⟨B, hB⟩ := (hT F E σ hc d J hJ).2.2.2.2.2.2.2 Ω hΩ
  refine ⟨max C 0 * (B : ℝ) ^ k, k, by positivity, fun h δ hδ t ht' κ hκ e => ?_⟩
  have e2 : δ⁻¹ * fr.a t = h * κ⁻¹ := by
    rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, e, mul_inv_cancel_right]
  have h3 := (hC t ht').2 δ⁻¹ (inv_mem hδ)
  rw [e2] at h3
  have h4 : (ht (h * κ⁻¹) : ℝ) ≤ B * ht h := by
    have hb : ht κ⁻¹ ≤ B := by rw [ht_inv]; exact hB κ hκ
    have := (ht_mul_le h κ⁻¹).trans (mul_le_mul_right hb _)
    rw [mul_comm] at this
    exact_mod_cast this
  calc _ ≤ C * (ht (h * κ⁻¹) : ℝ) ^ k := h3
    _ ≤ max C 0 * ((B : ℝ) * ht h) ^ k := by gcongr; exact le_max_left _ _
    _ = _ := by rw [mul_pow, mul_assoc]

theorem latSum_redH (hT : GrpTop) (hS : SiegelAll) (hI : LatInv) (hK : LatCpt) (hA : LatArch) (hc : IsCMExt F E σ)
    (τ : ∀ w : InfinitePlace F, EmbOver E w) {n d : ℕ} {J : Matrix (Fin n) (Fin n) E} {J' : Matrix (Fin d) (Fin d) E}
    (hJ : EpsHerm σ J) (hJ' : EpsHerm σ J') (N : ℕ) :
    ∃ k : ℕ, ∀ C, IsCompact C → ∃ (C' : Set (Ten F E n d)) (K : ℝ), IsCompact C' ∧ 0 ≤ K ∧ ∀ (g : UA σ J) (h : UA σ J'),
      latSum τ C N Set.univ g h ≤ ENNReal.ofReal ((K * (ht h : ℝ) ^ k) ^ 2) * latSum τ C' N Set.univ g (1 : UA σ J') := by
  obtain ⟨fr, hg, -, ⟨Ω, hΩ, hcov⟩, -, hht⟩ := hS F E σ hc d J' hJ'
  obtain ⟨A, k, hA0, hAk⟩ := exp_le_ht hT hc hJ' hht hΩ
  refine ⟨k * N, fun C hC => ?_⟩
  obtain ⟨C₁, K₁, hC₁, h₁⟩ := hK F E σ hc τ n d J J' hJ hJ' {1} Ω isCompact_singleton hΩ C N hC
  obtain ⟨C₂, K₂, hC₂, h₂⟩ := hA F E σ hc τ n d J J' hJ hJ' fr hg C₁ N hC₁
  refine ⟨C₂, K₁ * K₂ * A ^ N + 1, hC₂, by positivity, fun g h => ?_⟩
  obtain ⟨δ, hδ, t, ht', κ, hκ, e⟩ := hcov h
  have e1 := hI F E σ hc τ n d J J' hJ hJ' C N Set.univ (by simp) 1 (one_mem _) δ hδ g h
  rw [← e1, e, one_mul]
  have e2 := h₁ Set.univ g (fr.a t) 1 rfl κ hκ
  rw [mul_one] at e2
  refine e2.trans ((mul_le_mul_right (h₂ Set.univ g t ht') _).trans ?_)
  rw [← mul_assoc, ← mul_assoc]
  refine mul_le_mul_left ?_ _
  rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  have h1 : (1 : ℝ) ≤ (ht h : ℝ) ^ (k * N) := one_le_pow₀ (by exact_mod_cast one_le_ht h)
  have h3 : Real.exp (N * ∑ j, t j) ≤ A ^ N * (ht h : ℝ) ^ (k * N) := by
    rw [Real.exp_nat_mul, pow_mul, ← mul_pow]
    exact pow_le_pow_left₀ (Real.exp_pos _).le (hAk h δ hδ t ht' κ hκ e) _
  have h4 : (0 : ℝ) ≤ K₁ * K₂ * A ^ N := by positivity
  have h5 : (1 : ℝ) ≤ (K₁ * K₂ * A ^ N + 1) * (ht h : ℝ) ^ (k * N) := by nlinarith
  calc (K₁ : ℝ) * K₂ * Real.exp (N * ∑ j, t j) ≤ K₁ * K₂ * (A ^ N * (ht h : ℝ) ^ (k * N)) := by gcongr
    _ ≤ (K₁ * K₂ * A ^ N + 1) * (ht h : ℝ) ^ (k * N) := by nlinarith
    _ ≤ _ := by nlinarith

end PositivityTheory.ThKEst

end
