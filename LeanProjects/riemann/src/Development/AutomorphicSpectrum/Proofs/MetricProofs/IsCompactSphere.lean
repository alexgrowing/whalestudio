import Mathlib

open Matrix Filter Topology
open scoped BigOperators ComplexOrder

namespace GlobalTheory.CompanionTheory.GramCompact

private theorem exists_sum_norm_sq_eq_one_and_eq_sqrt_smul {m : Type} [Fintype m] (w : m → ℂ)
    (hw : 0 < ∑ k, ‖w k‖ ^ 2) :
    ∃ v : m → ℂ, ∑ k, ‖v k‖ ^ 2 = 1 ∧
      w = ((Real.sqrt (∑ k, ‖w k‖ ^ 2) : ℝ) : ℂ) • v := by
  have ht : 0 < Real.sqrt (∑ k, ‖w k‖ ^ 2) := Real.sqrt_pos.mpr hw
  have ht2 : Real.sqrt (∑ k, ‖w k‖ ^ 2) ^ 2 = ∑ k, ‖w k‖ ^ 2 := Real.sq_sqrt hw.le
  refine ⟨(((Real.sqrt (∑ k, ‖w k‖ ^ 2))⁻¹ : ℝ) : ℂ) • w, ?_, ?_⟩
  · have h : ∀ k, ‖((((Real.sqrt (∑ j, ‖w j‖ ^ 2))⁻¹ : ℝ) : ℂ) • w) k‖ ^ 2 =
        (Real.sqrt (∑ j, ‖w j‖ ^ 2) ^ 2)⁻¹ * ‖w k‖ ^ 2 := by
      intro k
      rw [Pi.smul_apply, norm_smul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs, inv_pow]
    simp only [h]
    rw [← Finset.mul_sum, ht2, inv_mul_cancel₀ hw.ne']
  · rw [smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ ht.ne', Complex.ofReal_one, one_smul]

private theorem continuousOn_re_star_dotProduct_mulVec {X : Type} [TopologicalSpace X] {K : Set X}
    {m : Type} [Fintype m] {H : X → Matrix m m ℂ} (hH : ContinuousOn H K) (T : Set (m → ℂ)) :
    ContinuousOn (fun p : X × (m → ℂ) => (star p.2 ⬝ᵥ (H p.1 *ᵥ p.2)).re) (K ×ˢ T) := by
  have hd : Continuous (fun q : Matrix m m ℂ × (m → ℂ) => star q.2 ⬝ᵥ (q.1 *ᵥ q.2)) := by
    apply Continuous.dotProduct
    · exact continuous_snd.star
    · exact Continuous.matrix_mulVec continuous_fst continuous_snd
  have hfst : ContinuousOn (H ∘ Prod.fst) (K ×ˢ T) :=
    ContinuousOn.comp hH continuousOn_fst (fun p hp => (Set.mem_prod.mp hp).1)
  have h2 : ContinuousOn (fun p : X × (m → ℂ) => ((H ∘ Prod.fst) p, p.2)) (K ×ˢ T) :=
    ContinuousOn.prodMk hfst continuousOn_snd
  have h3 := Continuous.comp_continuousOn (Continuous.comp Complex.continuous_re hd) h2
  exact h3

theorem isCompact_sphere (m : Type) [Fintype m] :
    IsCompact {w : m → ℂ | ∑ k, ‖w k‖ ^ 2 = 1} := by
  apply Metric.isCompact_of_isClosed_isBounded
  · exact isClosed_eq (by fun_prop) continuous_const
  · refine (Metric.isBounded_closedBall (x := (0 : m → ℂ)) (r := 1)).subset ?_
    intro w hw
    have hw' : ∑ k, ‖w k‖ ^ 2 = 1 := hw
    rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg zero_le_one]
    intro k
    have h1 : ‖w k‖ ^ 2 ≤ 1 := by
      calc ‖w k‖ ^ 2 ≤ ∑ j, ‖w j‖ ^ 2 :=
            Finset.single_le_sum (f := fun j => ‖w j‖ ^ 2) (fun j _ => by positivity)
              (Finset.mem_univ k)
        _ = 1 := hw'
    nlinarith [norm_nonneg (w k)]

theorem form_smul {m : Type} [Fintype m] (A : Matrix m m ℂ) (r : ℝ) (w : m → ℂ) :
    (star ((r : ℂ) • w) ⬝ᵥ (A *ᵥ ((r : ℂ) • w))).re = r ^ 2 * (star w ⬝ᵥ (A *ᵥ w)).re := by
  have hs : star ((r : ℂ) • w) = (r : ℂ) • star w := by
    ext k
    simp
  rw [hs, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul]
  simp only [smul_eq_mul]
  rw [← mul_assoc, ← Complex.ofReal_mul, Complex.re_ofReal_mul]
  ring

theorem exists_bounds (X : Type) [TopologicalSpace X] (K : Set X) (m : Type) [Fintype m]
    [DecidableEq m] (H : X → Matrix m m ℂ) (hK : IsCompact K) (hH : ContinuousOn H K)
    (hpos : ∀ x ∈ K, (H x).PosDef) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ x ∈ K, ∀ w : m → ℂ,
      C⁻¹ * ∑ k, ‖w k‖ ^ 2 ≤ (star w ⬝ᵥ (H x *ᵥ w)).re ∧
        (star w ⬝ᵥ (H x *ᵥ w)).re ≤ C * ∑ k, ‖w k‖ ^ 2 := by
  obtain ⟨T, hT⟩ : ∃ T : Set (m → ℂ), T = {w : m → ℂ | ∑ k, ‖w k‖ ^ 2 = 1} := ⟨_, rfl⟩
  have hKS : IsCompact (K ×ˢ T) := hT ▸ hK.prod (GlobalTheory.CompanionTheory.GramCompact.isCompact_sphere m)
  have hfc := continuousOn_re_star_dotProduct_mulVec hH T
  have hfpos : ∀ x ∈ K, ∀ w ∈ T, 0 < (star w ⬝ᵥ (H x *ᵥ w)).re := by
    intro x hx w hw
    rw [hT, Set.mem_setOf_eq] at hw
    have hw0 : w ≠ 0 := by
      rintro rfl
      simp at hw
    exact (Complex.pos_iff.mp ((Matrix.posDef_iff_dotProduct_mulVec.mp (hpos x hx)).2 hw0)).1
  obtain ⟨c, hc0, hc⟩ : ∃ c : ℝ, 0 < c ∧ ∀ x ∈ K, ∀ w ∈ T,
      c ≤ (star w ⬝ᵥ (H x *ᵥ w)).re := by
    rcases (K ×ˢ T).eq_empty_or_nonempty with h | h
    · refine ⟨1, one_pos, fun x hx w hw => ?_⟩
      have hm : (x, w) ∈ K ×ˢ T := Set.mk_mem_prod hx hw
      rw [h] at hm
      exact absurd hm (Set.notMem_empty _)
    · obtain ⟨p₀, hp₀, hmin⟩ := hKS.exists_isMinOn h hfc
      refine ⟨_, hfpos p₀.1 (Set.mem_prod.mp hp₀).1 p₀.2 (Set.mem_prod.mp hp₀).2,
        fun x hx w hw => ?_⟩
      exact hmin (Set.mk_mem_prod hx hw)
  obtain ⟨M, hM⟩ := hKS.exists_bound_of_continuousOn hfc
  have hC1 : c⁻¹ ≤ max 1 (max c⁻¹ M) := (le_max_left _ _).trans (le_max_right _ _)
  have hCM : M ≤ max 1 (max c⁻¹ M) := (le_max_right _ _).trans (le_max_right _ _)
  have hCc : (max 1 (max c⁻¹ M))⁻¹ ≤ c := inv_le_of_inv_le₀ hc0 hC1
  refine ⟨max 1 (max c⁻¹ M), le_max_left _ _, ?_⟩
  intro x hx w
  have hs0 : 0 ≤ ∑ k, ‖w k‖ ^ 2 := Finset.sum_nonneg (fun k _ => by positivity)
  rcases hs0.eq_or_lt with hs | hspos
  · have hw : w = 0 := by
      funext k
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => by positivity)).mp hs.symm k
        (Finset.mem_univ k)
      simpa using this
    subst hw
    simp
  · obtain ⟨v, hv1, hwv⟩ := exists_sum_norm_sq_eq_one_and_eq_sqrt_smul w hspos
    have hvT : v ∈ T := by
      rw [hT]
      exact hv1
    have hq : (star w ⬝ᵥ (H x *ᵥ w)).re =
        (∑ k, ‖w k‖ ^ 2) * (star v ⬝ᵥ (H x *ᵥ v)).re := by
      conv_lhs => rw [hwv]
      rw [GlobalTheory.CompanionTheory.GramCompact.form_smul, Real.sq_sqrt hs0]
    have h1 : c ≤ (star v ⬝ᵥ (H x *ᵥ v)).re := hc x hx v hvT
    have h2 : (star v ⬝ᵥ (H x *ᵥ v)).re ≤ M := by
      have h3 : ‖(star v ⬝ᵥ (H x *ᵥ v)).re‖ ≤ M := hM (x, v) (Set.mk_mem_prod hx hvT)
      rw [Real.norm_eq_abs] at h3
      exact (le_abs_self _).trans h3
    rw [hq]
    have h4 := mul_le_mul_of_nonneg_right hCc hspos.le
    have h5 := mul_le_mul_of_nonneg_right h1 hspos.le
    have h6 := mul_le_mul_of_nonneg_right (h2.trans hCM) hspos.le
    constructor
    · linarith
    · linarith

end GlobalTheory.CompanionTheory.GramCompact
