import Mathlib

noncomputable section

set_option linter.unusedSectionVars false

namespace PositivityTheory.ThKEnd.Two

open MeasureTheory Topology Filter
open scoped Pointwise

variable {G X : Type} [Group G] [TopologicalSpace G]

structure Bump (V : Set G) (η : G → ℝ) : Prop where
  cont : Continuous η
  cpt : HasCompactSupport η
  sub : tsupport η ⊆ V
  nonneg : ∀ y, 0 ≤ η y
  one : η 1 ≠ 0

structure Cusp (Γ : Subgroup G) (n : X → G) (a : G) : Prop where
  siegel : ∃ Ω, IsCompact Ω ∧ ∀ g, ∃ γ ∈ Γ, ∃ k : ℕ, ∃ κ ∈ Ω, γ * g = a ^ k * κ
  lip : ∀ V ∈ 𝓝 (1 : G), ∃ η, Bump V η ∧ ∀ Ω : Set G, IsCompact Ω → ∃ (D : ℝ) (Ω' : Set G), IsCompact Ω' ∧ ∀ x (k : ℕ),
    ∃ γ ∈ Γ, ∃ u ∈ Ω', γ * n x * a ^ k = a ^ k * u ∧ ∀ κ ∈ Ω, ∀ y, |η (κ⁻¹ * (u⁻¹ * y)) - η (κ⁻¹ * y)| ≤ D / 2 ^ k

def Gr (a : G) (m : ℕ) (φ : G → ℂ) : Prop := ∀ Ω : Set G, IsCompact Ω → ∃ C : ℝ, ∀ k : ℕ, ∀ κ ∈ Ω, ‖φ (a ^ k * κ)‖ ≤ C * (2 ^ k) ^ m

structure Dat [MeasurableSpace X] (Γ : Subgroup G) (n : X → G) (a : G) (lam : Measure X) (l : ℂ) (φ c : G → ℂ) : Prop where
  cont : Continuous φ
  inv : ∀ γ ∈ Γ, ∀ g, φ (γ * g) = φ g
  contc : Continuous c
  av : ∀ g, c g = ∫ x, φ (n x * g) ∂lam
  law : ∀ g, c (a * (a * g)) - c (a * g) = l * (c (a * g) - c g)

def conv [MeasurableSpace G] (μ : Measure G) (η : G → ℝ) (φ : G → ℂ) : G → ℂ := fun g => ∫ y, φ (g * y) * η y ∂μ

variable [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G]
  [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X] {Γ : Subgroup G} {n : X → G} {a : G} {lam : Measure X}
  [IsProbabilityMeasure lam] {l : ℂ} {φ c : G → ℂ} {V : Set G} {η : G → ℝ} (μ : Measure G) [μ.IsHaarMeasure]

theorem Bump.int (h : Bump V η) (hφ : Continuous φ) (g : G) : Integrable (fun y => φ (g * y) * η y) μ := by
  have := h.cont
  exact Continuous.integrable_of_hasCompactSupport (by fun_prop)
    (HasCompactSupport.mul_left (h.cpt.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp)))

theorem Bump.conv_cont (h : Bump V η) (hφ : Continuous φ) : Continuous (conv μ η φ) := by
  have := h.cont
  have e : conv μ η φ = fun g => ∫ y in tsupport η, φ (g * y) * η y ∂μ := funext fun g =>
    (setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy => by simp [image_eq_zero_of_notMem_tsupport hy]).symm
  rw [e]
  exact continuous_parametric_integral_of_continuous (by fun_prop) h.cpt

theorem Bump.zero (D : G → ℂ) (hD : Continuous D) (g : G) (h : ∀ V ∈ 𝓝 (1 : G), ∃ η, Bump V η ∧ conv μ η D g = 0) : D g = 0 := by
  by_contra h0
  have hc : Continuous fun y => (D (g * y) / D g).re := by fun_prop
  obtain ⟨η, hη, e⟩ := h {y | 0 < (D (g * y) / D g).re} ((isOpen_lt continuous_const hc).mem_nhds (by simp [h0]))
  have hi := (hη.int μ hD g).div_const (D g)
  have h1 : ∫ y, (D (g * y) / D g).re * η y ∂μ = 0 := by
    have := congrArg (fun z => (z / D g).re) e
    simp only [conv, zero_div, Complex.zero_re] at this
    rw [← integral_div, ← RCLike.re_to_complex, ← integral_re hi] at this
    rw [← this]
    congr 1
    funext y
    rw [mul_div_right_comm]
    simp
  have := hη.cont
  refine (Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := 1) (by fun_prop) hη.cpt.mul_left (fun y => ?_)
    (by simp [h0, hη.one])).ne' h1
  by_cases hy : y ∈ tsupport η
  · exact mul_nonneg (hη.sub hy).le (hη.nonneg y)
  · simp [image_eq_zero_of_notMem_tsupport hy]

omit [MeasurableSpace G] [BorelSpace G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [TopologicalSpace X]
  [OpensMeasurableSpace X] [IsProbabilityMeasure lam] in
theorem Dat.bound (hC : Cusp Γ n a) (h : Dat Γ n a lam l φ c) {K : Set G} (hK : IsCompact K) :
    ∃ M, ∀ x, ∀ g ∈ K, ‖φ (n x * g)‖ ≤ M := by
  obtain ⟨η, -, h2⟩ := hC.lip _ univ_mem
  obtain ⟨D, Ω', h3, h4⟩ := h2 ∅ isCompact_empty
  obtain ⟨M, hM⟩ := (h3.mul hK).exists_bound_of_continuousOn h.cont.continuousOn
  refine ⟨M, fun x g hg => ?_⟩
  obtain ⟨γ, h5, u, h6, h7, -⟩ := h4 x 0
  rw [pow_zero, mul_one, one_mul] at h7
  rw [← h.inv γ h5, ← mul_assoc, h7]
  exact hM _ (Set.mul_mem_mul h6 hg)

theorem Dat.conv (hC : Cusp Γ n a) (hn : Continuous n) (h : Dat Γ n a lam l φ c) (hη : Bump V η) :
    Dat Γ n a lam l (conv μ η φ) (conv μ η c) := by
  refine ⟨hη.conv_cont μ h.cont, fun γ hγ g => ?_, hη.conv_cont μ h.contc, fun g => ?_, fun g => ?_⟩
  · simp only [Two.conv, mul_assoc, h.inv γ hγ]
  · simp only [Two.conv, h.av, ← integral_mul_const, mul_assoc]
    refine integral_integral_swap ?_
    obtain ⟨M, hM⟩ := h.bound hC (hη.cpt.isCompact.image (continuous_const_mul g))
    have := h.cont
    have := hη.cont
    refine Integrable.mono' ((hη.cont.integrable_of_hasCompactSupport hη.cpt).mul_prod (integrable_const M))
      (Continuous.aestronglyMeasurable (by fun_prop)) (.of_forall fun z => ?_)
    by_cases hy : z.1 ∈ tsupport η
    · simp only [Function.uncurry, norm_mul, Complex.norm_real, Real.norm_of_nonneg (hη.nonneg _)]
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_left (hM _ _ ⟨_, hy, rfl⟩) (hη.nonneg _)
    · simp [Function.uncurry, image_eq_zero_of_notMem_tsupport hy]
  · simp only [Two.conv]
    rw [← integral_sub (hη.int μ h.contc _) (hη.int μ h.contc _), ← integral_sub (hη.int μ h.contc _) (hη.int μ h.contc _),
      ← integral_const_mul]
    congr 1
    funext y
    have := h.law (g * y)
    simp only [mul_assoc]
    linear_combination (η y : ℂ) * this

omit [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G]
  [TopologicalSpace X] [OpensMeasurableSpace X] [IsProbabilityMeasure lam] in
theorem Dat.pow (h : Dat Γ n a lam l φ c) (k : ℕ) (g : G) : c (a * (a ^ k * g)) - c (a ^ k * g) = l ^ k * (c (a * g) - c g) := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ' a, mul_assoc, h.law, ih, pow_succ' l, mul_assoc]

omit [MeasurableSpace G] [BorelSpace G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G]
  [TopologicalSpace X] [OpensMeasurableSpace X] [IsProbabilityMeasure lam] in
theorem Dat.gr (h : Dat Γ n a lam l φ c) (hl : ‖l‖ < 1) : Gr a 0 c := fun Ω hΩ => by
  have := h.contc
  obtain ⟨M, hM⟩ := hΩ.exists_bound_of_continuousOn h.contc.continuousOn
  obtain ⟨M', hM'⟩ := hΩ.exists_bound_of_continuousOn (f := fun g => c (a * g) - c g) (Continuous.continuousOn (by fun_prop))
  refine ⟨M + (1 - ‖l‖)⁻¹ * M', fun k κ hκ => ?_⟩
  have e : c (a ^ k * κ) = c κ + (∑ i ∈ Finset.range k, l ^ i) * (c (a * κ) - c κ) := by
    induction k with
    | zero => simp
    | succ k ih => rw [Finset.sum_range_succ, pow_succ' a, mul_assoc]; linear_combination ih + h.pow k κ
  have e2 : ‖∑ i ∈ Finset.range k, l ^ i‖ ≤ (1 - ‖l‖)⁻¹ := by
    refine (norm_sum_le _ _).trans ?_
    simp only [norm_pow]
    rw [← tsum_geometric_of_lt_one (norm_nonneg l) hl]
    exact (summable_geometric_of_lt_one (norm_nonneg l) hl).sum_le_tsum _ fun _ _ => by positivity
  rw [pow_zero, mul_one, e]
  refine (norm_add_le _ _).trans (add_le_add (hM κ hκ) ?_)
  rw [norm_mul]
  exact mul_le_mul e2 (hM' κ hκ) (norm_nonneg _) ((norm_nonneg _).trans e2)

theorem Dat.step (hC : Cusp Γ n a) (hn : Continuous n) (h : Dat Γ n a lam l φ c) (hl : ‖l‖ < 1) {m : ℕ} (hm : Gr a (m + 1) φ)
    (hV : V ∈ 𝓝 (1 : G)) : ∃ η, Bump V η ∧ Gr a m (Two.conv μ η φ) := by
  obtain ⟨η, hη, h2⟩ := hC.lip V hV
  refine ⟨η, hη, fun Ω hΩ => ?_⟩
  have h' := h.conv μ hC hn hη
  obtain ⟨D, Ω', h3, h4⟩ := h2 Ω hΩ
  obtain ⟨C₀, hC₀⟩ := h'.gr hl Ω hΩ
  have hK : IsCompact (Ω' * (Ω * tsupport η) ∪ Ω * tsupport η) := (h3.mul (hΩ.mul hη.cpt)).union (hΩ.mul hη.cpt)
  obtain ⟨C, hCC⟩ := hm _ hK
  set K := Ω' * (Ω * tsupport η) ∪ Ω * tsupport η
  refine ⟨C₀ + C * D * μ.real K, fun k κ hκ => ?_⟩
  have key : ∀ x, ‖Two.conv μ η φ (a ^ k * κ) - Two.conv μ η φ (n x * (a ^ k * κ))‖ ≤ C * D * μ.real K * (2 ^ k) ^ m := fun x => by
    obtain ⟨γ, h5, u, h6, h7, h8⟩ := h4 x k
    have e : ∀ z, Two.conv μ η φ (a ^ k * z) = ∫ y, φ (a ^ k * y) * η (z⁻¹ * y) ∂μ := fun z => by
      rw [Two.conv, ← integral_mul_left_eq_self _ z⁻¹]
      simp only [mul_assoc, mul_inv_cancel_left]
    have i : ∀ z, Integrable (fun y => φ (a ^ k * y) * η (z⁻¹ * y)) μ := fun z => by
      simpa only [mul_assoc, mul_inv_cancel_left] using (hη.int μ h.cont (a ^ k * z)).comp_mul_left z⁻¹
    rw [← h'.inv γ h5 (n x * _), ← mul_assoc γ, ← mul_assoc _ _ κ, h7, mul_assoc _ u, e, e, ← integral_sub (i _) (i _),
      ← setIntegral_eq_integral_of_forall_compl_eq_zero (s := K) fun y hy => ?_]
    · refine (norm_setIntegral_le_of_norm_le_const (C := C * D * (2 ^ k) ^ m) hK.measure_lt_top fun y hy => ?_).trans_eq (by ring)
      rw [← mul_sub, norm_mul, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_sub_comm, mul_inv_rev, mul_assoc κ⁻¹]
      refine (mul_le_mul (hCC k y hy) (h8 κ hκ y) (abs_nonneg _) ((norm_nonneg _).trans (hCC k y hy))).trans_eq ?_
      field_simp
      ring
    · have z1 : η (κ⁻¹ * y) = 0 := image_eq_zero_of_notMem_tsupport fun hh => hy (Or.inr ⟨κ, hκ, _, hh, by simp⟩)
      have z2 : η ((u * κ)⁻¹ * y) = 0 := image_eq_zero_of_notMem_tsupport fun hh =>
        hy (Or.inl ⟨u, h6, _, ⟨κ, hκ, _, hh, rfl⟩, by simp [mul_assoc]⟩)
      rw [z1, z2, sub_self]
  obtain ⟨M, hM⟩ := h'.bound hC (isCompact_singleton (x := a ^ k * κ))
  have := h'.cont
  have hi : Integrable (fun x => Two.conv μ η φ (n x * (a ^ k * κ))) lam :=
    .of_bound (Continuous.aestronglyMeasurable (by fun_prop)) M (.of_forall fun x => hM x _ rfl)
  have e : Two.conv μ η φ (a ^ k * κ) = Two.conv μ η c (a ^ k * κ) +
      ∫ x, (Two.conv μ η φ (a ^ k * κ) - Two.conv μ η φ (n x * (a ^ k * κ))) ∂lam := by
    rw [integral_sub (integrable_const _) hi, ← h'.av]; simp
  have h9 := hC₀ k κ hκ
  rw [pow_zero, mul_one] at h9
  have h10 : (1 : ℝ) ≤ (2 ^ k) ^ m := one_le_pow₀ (one_le_pow₀ one_le_two)
  rw [e, add_mul]
  refine (norm_add_le _ _).trans (add_le_add (h9.trans (le_mul_of_one_le_right ((norm_nonneg _).trans h9) h10)) ?_)
  simpa using norm_integral_le_of_norm_le_const (μ := lam) (.of_forall key)

theorem kill_ind (hC : Cusp Γ n a) (hn : Continuous n) (hl : ‖l‖ < 1) (P : (G → ℂ) → (G → ℂ) → Prop)
    (h0 : ∀ φ c, Dat Γ n a lam l φ c → (∃ M, ∀ g, ‖φ g‖ ≤ M) → P φ c)
    (h1 : ∀ φ c, Dat Γ n a lam l φ c → (∀ V ∈ 𝓝 (1 : G), ∃ η, Bump V η ∧ P (conv μ η φ) (conv μ η c)) → P φ c)
    (m : ℕ) : ∀ φ c, Dat Γ n a lam l φ c → Gr a m φ → P φ c := by
  induction m with
  | zero =>
    intro φ c h hm
    obtain ⟨Ω, hΩ, hs⟩ := hC.siegel
    obtain ⟨C, hCC⟩ := hm Ω hΩ
    refine h0 φ c h ⟨C, fun g => ?_⟩
    obtain ⟨γ, a1, k, κ, a2, a3⟩ := hs g
    simpa [← a3, h.inv γ a1] using hCC k κ a2
  | succ m ih =>
    intro φ c h hm
    refine h1 φ c h fun V hV => ?_
    obtain ⟨η, a1, a2⟩ := h.step μ hC hn hl hm hV
    exact ⟨η, a1, ih _ _ (h.conv μ hC hn a1) a2⟩

theorem kill (hC : Cusp Γ n a) (hn : Continuous n) (hl : ‖l‖ < 1) {m : ℕ} (h : Dat Γ n a lam l φ c) (hm : Gr a m φ) (g : G) :
    c (a * g) = c g := by
  refine kill_ind (Measure.haar) hC hn hl (fun _ c => ∀ g, c (a * g) = c g) (fun φ c h ⟨M, hM⟩ g => ?_) (fun φ c h h1 g => ?_) m φ c h hm g
  · have hc : ∀ g, ‖c g‖ ≤ M := fun g => by
      rw [h.av]
      simpa using norm_integral_le_of_norm_le_const (μ := lam) (.of_forall fun x => hM (n x * g))
    have t : Tendsto (fun k : ℕ => ‖l‖ ^ k * (M + M)) atTop (𝓝 (0 * (M + M))) :=
      (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg l) hl).mul_const _
    rw [zero_mul] at t
    refine sub_eq_zero.1 (norm_le_zero_iff.1 (ge_of_tendsto' t fun k => ?_))
    have := h.pow k ((a ^ k)⁻¹ * g)
    rw [mul_inv_cancel_left] at this
    rw [this, norm_mul, norm_pow]
    exact mul_le_mul_of_nonneg_left ((norm_sub_le _ _).trans (add_le_add (hc _) (hc _))) (by positivity)
  · have := h.contc
    refine sub_eq_zero.1 (Bump.zero Measure.haar (fun g => c (a * g) - c g) (by fun_prop) g fun V hV => ?_)
    obtain ⟨η, a1, a2⟩ := h1 V hV
    refine ⟨η, a1, ?_⟩
    rw [← sub_eq_zero.2 (a2 g), conv, conv, conv, ← integral_sub (a1.int _ h.contc _) (a1.int _ h.contc _)]
    simp only [sub_mul, mul_assoc]

end PositivityTheory.ThKEnd.Two

end
