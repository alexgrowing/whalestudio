import Mathlib
import ReciprocityTheory.ThetaQuasiPeriods.ThetaQuasiPeriodStatement
import ReciprocityTheory.ThetaQuasiPeriods.Transl
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsEventuallyNormRiemannThetaTermLe

open Complex Matrix ReciprocityTheory.PTheta

noncomputable section

namespace GlobalTheory

variable {ι : Type*} [Fintype ι]

open Complex Matrix in
variable {ι : Type*} [Fintype ι] in
private lemma im_quadForm_pos_of_mem_thetaDomain {τ : Matrix ι ι ℂ} (hτ : τ ∈ _root_.ReciprocityTheory.PTheta.ThetaDomain ι)
    (x : ι → ℝ) (hx : x ≠ 0) : 0 < x ⬝ᵥ τ.map Complex.im *ᵥ x := by
  have h : ((τ.map Complex.im) + (τ.map Complex.im).transpose).PosDef := by
    unfold _root_.ReciprocityTheory.PTheta.ThetaDomain at hτ
    exact hτ
  have h1 : x ⬝ᵥ (τ.map Complex.im)ᵀ *ᵥ x = x ⬝ᵥ τ.map Complex.im *ᵥ x := by
    rw [dotProduct_mulVec, vecMul_transpose, dotProduct_comm]
  have h2 := h.dotProduct_mulVec_pos hx
  rw [add_mulVec, dotProduct_add, star_trivial, h1] at h2
  linarith

open Complex Matrix in
variable {ι : Type*} [Fintype ι] in
private lemma exists_uniform_im_quadForm_lower_bound_on_compact {K : Set ((ι → ℂ) × (ι → ι → ℂ))}
    (hK : IsCompact K) (hKd : ∀ p ∈ K, Matrix.of p.2 ∈ _root_.ReciprocityTheory.PTheta.ThetaDomain ι) :
    ∃ c > 0, ∀ p ∈ K, ∀ x : ι → ℝ,
      c * x ⬝ᵥ x ≤ x ⬝ᵥ (Matrix.of p.2).map Complex.im *ᵥ x := by
  classical
  set g : ((ι → ℂ) × (ι → ι → ℂ)) × (ι → ℝ) → ℝ :=
    fun q => q.2 ⬝ᵥ (Matrix.of q.1.2).map Complex.im *ᵥ q.2 with hg_def
  have hg : Continuous g := by
    simp only [hg_def, dotProduct, mulVec, Matrix.map_apply, Matrix.of_apply]
    fun_prop
  have hS : IsCompact (K ×ˢ Metric.sphere (0 : ι → ℝ) 1) := hK.prod (isCompact_sphere 0 1)
  rcases (K ×ˢ Metric.sphere (0 : ι → ℝ) 1).eq_empty_or_nonempty with he | hne
  · refine ⟨1, one_pos, fun p hp x => ?_⟩
    by_cases hx : x = 0
    · subst hx; simp
    · exfalso
      have hmem : (p, ‖x‖⁻¹ • x) ∈ K ×ˢ Metric.sphere (0 : ι → ℝ) 1 :=
        ⟨hp, by simp [norm_smul, hx]⟩
      rw [he] at hmem
      exact hmem
  · obtain ⟨q, hq, hmin⟩ := hS.exists_isMinOn hne hg.continuousOn
    have hq0 : q.2 ≠ 0 := by
      intro h
      have := hq.2
      simp [h] at this
    have hm : 0 < g q := im_quadForm_pos_of_mem_thetaDomain (hKd q.1 hq.1) q.2 hq0
    refine ⟨g q / (Fintype.card ι + 1), by positivity, fun p hp x => ?_⟩
    by_cases hx : x = 0
    · subst hx; simp
    have ht : 0 < ‖x‖ := norm_pos_iff.mpr hx
    have h1 : g q ≤ g (p, ‖x‖⁻¹ • x) := hmin ⟨hp, by simp [norm_smul, ht.ne']⟩
    have h2 : g (p, ‖x‖⁻¹ • x) =
        ‖x‖⁻¹ ^ 2 * (x ⬝ᵥ (Matrix.of p.2).map Complex.im *ᵥ x) := by
      simp only [hg_def, mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul]
      ring
    have h3 : x ⬝ᵥ x ≤ Fintype.card ι * ‖x‖ ^ 2 := by
      simp only [dotProduct]
      calc ∑ i, x i * x i ≤ ∑ _i : ι, ‖x‖ ^ 2 := Finset.sum_le_sum fun i _ => by
            have := norm_le_pi_norm x i
            rw [Real.norm_eq_abs] at this
            nlinarith [abs_nonneg (x i), abs_mul_abs_self (x i)]
        _ = _ := by simp
    set Q := x ⬝ᵥ (Matrix.of p.2).map Complex.im *ᵥ x
    have h4 : g q * ‖x‖ ^ 2 ≤ Q := by
      rw [h2] at h1
      calc g q * ‖x‖ ^ 2 ≤ ‖x‖⁻¹ ^ 2 * Q * ‖x‖ ^ 2 := by gcongr
        _ = Q := by field_simp
    have hxx : 0 ≤ x ⬝ᵥ x := by
      simp only [dotProduct]
      exact Finset.sum_nonneg fun i _ => mul_self_nonneg (x i)
    calc g q / (Fintype.card ι + 1) * (x ⬝ᵥ x)
        ≤ g q / (Fintype.card ι + 1) * (Fintype.card ι * ‖x‖ ^ 2) := by gcongr
      _ ≤ g q * ‖x‖ ^ 2 := by
          rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
          nlinarith [mul_nonneg hm.le (sq_nonneg ‖x‖)]
      _ ≤ Q := h4

open Complex Matrix in
variable {ι : Type*} [Fintype ι] in

theorem _root_.GlobalTheory.thetaMTest_holds : _root_.ReciprocityTheory.PTheta.ThetaMTestStatement := by
  unfold _root_.ReciprocityTheory.PTheta.ThetaMTestStatement
  intro ι _ a K hK hKd
  obtain ⟨c, hc, hcK⟩ := exists_uniform_im_quadForm_lower_bound_on_compact hK hKd
  obtain ⟨S, hS⟩ := hK.exists_bound_of_continuousOn (f := fun p => p.1) continuous_fst.continuousOn
  refine ⟨_root_.GlobalTheory.riemannThetaBound a c S, _root_.GlobalTheory.summable_riemannThetaBound a hc S,
    fun b p hp l => ?_⟩
  exact _root_.GlobalTheory.norm_riemannThetaTerm_le a b (hcK p hp)
    (fun i => (_root_.GlobalTheory.abs_im_apply_le_norm p.1 i).trans (hS p hp)) l

open Complex Matrix in
variable {ι : Type*} [Fintype ι] in

theorem _root_.GlobalTheory.thetaSummable_holds : _root_.ReciprocityTheory.PTheta.ThetaSummableStatement := by
  have hM := _root_.GlobalTheory.thetaMTest_holds
  unfold _root_.ReciprocityTheory.PTheta.ThetaMTestStatement at hM
  unfold _root_.ReciprocityTheory.PTheta.ThetaSummableStatement
  intro ι _ a b z τ hτ
  obtain ⟨u, hu, hbound⟩ := hM ι a {(z, (τ : ι → ι → ℂ))} isCompact_singleton
    (fun p hp => by
      obtain rfl : p = (z, (τ : ι → ι → ℂ)) := hp
      exact hτ)
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun l => hbound b _ (Set.mem_singleton _) l) hu

open Complex Matrix in
variable {ι : Type*} [Fintype ι] in

theorem _root_.GlobalTheory.thetaMTest_and_thetaSummable : _root_.ReciprocityTheory.PTheta.ThetaMTestStatement ∧ _root_.ReciprocityTheory.PTheta.ThetaSummableStatement :=
  ⟨_root_.GlobalTheory.thetaMTest_holds, _root_.GlobalTheory.thetaSummable_holds⟩

end GlobalTheory
