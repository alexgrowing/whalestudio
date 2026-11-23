import Mathlib

noncomputable section

open Filter Complex PeriodPair
open scoped Topology ComplexConjugate Real

namespace GlobalTheory

variable (L : PeriodPair)

theorem isPreconnected_compl_lattice_sdiff (s : Set ℂ) :
    IsPreconnected ((L.lattice : Set ℂ) \ s)ᶜ :=
  (Set.Countable.isConnected_compl_of_one_lt_rank (by simp)
    (.mono Set.sdiff_subset (countable_of_Lindelof_of_discrete (X := L.lattice)))).2

theorem isPreconnected_compl_lattice : IsPreconnected (L.lattice : Set ℂ)ᶜ := by
  simpa using isPreconnected_compl_lattice_sdiff L ∅

theorem dense_compl_lattice : Dense (L.lattice : Set ℂ)ᶜ :=
  Set.Countable.dense_compl ℝ (countable_of_Lindelof_of_discrete (X := L.lattice))

theorem eventually_notMem_lattice (x : ℂ) : ∀ᶠ z in 𝓝[≠] x, z ∉ L.lattice := by
  filter_upwards [self_mem_nhdsWithin,
    mem_nhdsWithin_of_mem_nhds (L.compl_lattice_sdiff_singleton_mem_nhds x)] with w hw hw'
  simp_all

theorem add_notMem_lattice {L : PeriodPair} {z w : ℂ} (hz : z ∉ L.lattice) (hw : w ∈ L.lattice) :
    z + w ∉ L.lattice := fun h => hz (by simpa using sub_mem h hw)

theorem eventually_cofinite_le_norm (R : ℝ) : ∀ᶠ l : L.lattice in cofinite, R ≤ ‖(l : ℂ)‖ := by
  refine (isCompact_iff_finite.mp (isCompact_closedBall (0 : L.lattice) R)).subset ?_
  intro l hl
  simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_le] at hl
  simpa using hl.le

def zetaTerm (l z : ℂ) : ℂ := if l = 0 then 1 / z else 1 / (z - l) + 1 / l + z / l ^ 2

theorem zetaTerm_eq (l z : ℂ) : zetaTerm l z = 1 / (z - l) + 1 / l + z / l ^ 2 := by
  unfold zetaTerm
  split_ifs with h
  · simp [h]
  · rfl

theorem norm_zetaTerm_le {r : ℝ} (hr : 0 < r) {z : ℂ} (hz : ‖z‖ < r) {l : ℂ} (h : 2 * r ≤ ‖l‖) :
    ‖zetaTerm l z‖ ≤ 2 * r ^ 2 * ‖l‖ ^ (-3 : ℝ) := by
  have hl : 0 < ‖l‖ := by linarith
  have hl0 : l ≠ 0 := norm_pos_iff.1 hl
  have hzl : ‖l‖ / 2 ≤ ‖z - l‖ := by
    rw [norm_sub_rev]; exact .trans (by linarith) (norm_sub_norm_le l z)
  have hzl0 : z - l ≠ 0 := norm_pos_iff.1 (by linarith)
  have : zetaTerm l z = z ^ 2 / ((z - l) * l ^ 2) := by
    rw [zetaTerm_eq]; field_simp; ring
  rw [this]
  calc ‖z ^ 2 / ((z - l) * l ^ 2)‖ = ‖z‖ ^ 2 / (‖z - l‖ * ‖l‖ ^ 2) := by simp
    _ ≤ r ^ 2 / (‖l‖ / 2 * ‖l‖ ^ 2) := by gcongr
    _ = 2 * r ^ 2 / ‖l‖ ^ 3 := by field
    _ = _ := by norm_cast

def weierstrassZetaExcept (l₀ z : ℂ) : ℂ :=
  ∑' l : L.lattice, if (l : ℂ) = l₀ then 0 else zetaTerm l z

def weierstrassZeta (z : ℂ) : ℂ := ∑' l : L.lattice, zetaTerm l z

theorem hasSumLocallyUniformly_weierstrassZetaExcept (l₀ : ℂ) :
    HasSumLocallyUniformly
      (fun (l : L.lattice) (z : ℂ) => if (l : ℂ) = l₀ then 0 else zetaTerm l z)
      (weierstrassZetaExcept L l₀) := by
  refine L.hasSumLocallyUniformly_aux (u := fun r l => 2 * r ^ 2 * ‖l‖ ^ (-3 : ℝ)) _
    (fun _ _ => (ZLattice.summable_norm_rpow _ _ (by simp; norm_num)).mul_left _) fun r hr =>
    Filter.eventually_atTop.mpr ⟨2 * r, ?_⟩
  rintro _ h s hs l rfl
  split_ifs
  · rw [norm_zero]; positivity
  · exact norm_zetaTerm_le hr hs h

theorem hasSum_weierstrassZetaExcept (l₀ z : ℂ) :
    HasSum (fun l : L.lattice => if (l : ℂ) = l₀ then 0 else zetaTerm l z)
      (weierstrassZetaExcept L l₀ z) :=
  (hasSumLocallyUniformly_weierstrassZetaExcept L l₀).hasSum

theorem weierstrassZetaExcept_of_notMem {l₀ : ℂ} (h : l₀ ∉ L.lattice) :
    weierstrassZetaExcept L l₀ = weierstrassZeta L := by
  ext z
  refine tsum_congr fun l => if_neg ?_
  rintro rfl
  exact h l.2

theorem hasSumLocallyUniformly_weierstrassZeta :
    HasSumLocallyUniformly (fun (l : L.lattice) (z : ℂ) => zetaTerm l z) (weierstrassZeta L) := by
  convert hasSumLocallyUniformly_weierstrassZetaExcept L (L.ω₁ / 2) using 3 with l
  · rw [if_neg]; exact fun e => L.ω₁_div_two_notMem_lattice (e ▸ l.2)
  · rw [weierstrassZetaExcept_of_notMem _ L.ω₁_div_two_notMem_lattice]

theorem hasSum_weierstrassZeta (z : ℂ) :
    HasSum (fun l : L.lattice => zetaTerm l z) (weierstrassZeta L z) :=
  (hasSumLocallyUniformly_weierstrassZeta L).hasSum

theorem weierstrassZetaExcept_add {l₀ : ℂ} (h : l₀ ∈ L.lattice) (z : ℂ) :
    weierstrassZetaExcept L l₀ z + zetaTerm l₀ z = weierstrassZeta L z := by
  have h1 : HasSum (fun l : L.lattice => if l = ⟨l₀, h⟩ then zetaTerm l₀ z else 0)
      (zetaTerm l₀ z) := hasSum_ite_eq _ _
  refine ((hasSum_weierstrassZetaExcept L l₀ z).add h1).unique ?_
  convert hasSum_weierstrassZeta L z using 2 with l
  by_cases hl : (l : ℂ) = l₀
  · simp [hl, Subtype.ext_iff]
  · simp [hl, Subtype.ext_iff]

theorem weierstrassZeta_eq (z : ℂ) : weierstrassZeta L z = 1 / z +
    ∑' l : L.lattice, if (l : ℂ) = 0 then 0 else (1 / (z - l) + 1 / l + z / l ^ 2) := by
  rw [← weierstrassZetaExcept_add L (zero_mem _), add_comm, weierstrassZetaExcept]
  simp only [zetaTerm_eq]
  simp

theorem hasDerivAt_zetaTerm {l z : ℂ} (h : z ≠ l) :
    HasDerivAt (zetaTerm l) (-(1 / (z - l) ^ 2 - 1 / l ^ 2)) z := by
  have h0 : z - l ≠ 0 := sub_ne_zero.2 h
  have e : zetaTerm l = fun z => (z - l)⁻¹ + 1 / l + z / l ^ 2 := by
    ext; simp [zetaTerm_eq]
  rw [e]
  exact (((((hasDerivAt_id' z).sub_const l).fun_inv h0).add_const (1 / l)).fun_add
    ((hasDerivAt_id' z).div_const (l ^ 2))).congr_deriv (by ring)

theorem hasDerivAt_weierstrassZetaExcept (l₀ : ℂ) {z : ℂ} (hz : z ∈ ((L.lattice : Set ℂ) \ {l₀})ᶜ) :
    HasDerivAt (weierstrassZetaExcept L l₀) (-℘[L - l₀] z) z := by
  refine hasDerivAt_of_tendstoLocallyUniformlyOn (𝕜 := ℂ) L.isOpen_compl_lattice_sdiff
    (l := atTop)
    (f := fun (s : Finset L.lattice) z => ∑ l ∈ s, if (l : ℂ) = l₀ then 0 else zetaTerm l z)
    (f' := fun (s : Finset L.lattice) z =>
      -∑ l ∈ s, if (l : ℂ) = l₀ then 0 else (1 / (z - l) ^ 2 - 1 / l ^ 2))
    (g' := fun z => -℘[L - l₀] z)
    (L.hasSumLocallyUniformly_weierstrassPExcept l₀).tendstoLocallyUniformlyOn.neg
    (.of_forall fun s x hx => ?_)
    (fun x _ => hasSum_weierstrassZetaExcept L l₀ x) hz
  rw [← Finset.sum_neg_distrib]
  refine HasDerivAt.fun_sum fun l _ => ?_
  split_ifs with h
  · simpa using hasDerivAt_const x (0 : ℂ)
  · refine hasDerivAt_zetaTerm ?_
    rintro rfl
    exact hx ⟨l.2, h⟩

theorem analyticOnNhd_weierstrassZetaExcept (l₀ : ℂ) :
    AnalyticOnNhd ℂ (weierstrassZetaExcept L l₀) ((L.lattice : Set ℂ) \ {l₀})ᶜ :=
  DifferentiableOn.analyticOnNhd
    (fun _ hz => (hasDerivAt_weierstrassZetaExcept L l₀ hz).differentiableAt.differentiableWithinAt)
    L.isOpen_compl_lattice_sdiff

theorem analyticAt_weierstrassZetaExcept (l₀ : ℂ) :
    AnalyticAt ℂ (weierstrassZetaExcept L l₀) l₀ :=
  analyticOnNhd_weierstrassZetaExcept L l₀ l₀ (by simp)

theorem hasDerivAt_weierstrassZeta {z : ℂ} (hz : z ∉ L.lattice) :
    HasDerivAt (weierstrassZeta L) (-℘[L] z) z := by
  rw [← weierstrassZetaExcept_of_notMem L L.ω₁_div_two_notMem_lattice,
    ← L.weierstrassPExcept_of_notMem _ L.ω₁_div_two_notMem_lattice]
  exact hasDerivAt_weierstrassZetaExcept L _ fun h => hz h.1

theorem deriv_weierstrassZeta {z : ℂ} (hz : z ∉ L.lattice) :
    deriv (weierstrassZeta L) z = -℘[L] z := (hasDerivAt_weierstrassZeta L hz).deriv

theorem analyticOnNhd_weierstrassZeta :
    AnalyticOnNhd ℂ (weierstrassZeta L) (L.lattice : Set ℂ)ᶜ :=
  DifferentiableOn.analyticOnNhd
    (fun _ hz => (hasDerivAt_weierstrassZeta L hz).differentiableAt.differentiableWithinAt)
    L.isClosed_lattice.isOpen_compl

@[simp] theorem weierstrassZeta_neg (z : ℂ) : weierstrassZeta L (-z) = -weierstrassZeta L z := by
  simp only [weierstrassZeta, zetaTerm_eq]
  rw [← (Equiv.neg L.lattice).tsum_eq, ← tsum_neg]
  congr with l
  simp only [Equiv.neg_apply, NegMemClass.coe_neg]
  rw [show -z - -(l : ℂ) = -(z - l) by ring, div_neg, div_neg]
  ring

theorem weierstrassZeta_eq_inv_add (z : ℂ) :
    weierstrassZeta L z = 1 / z + weierstrassZetaExcept L 0 z := by
  rw [← weierstrassZetaExcept_add L (zero_mem _), add_comm, zetaTerm, if_pos rfl]

@[simp] theorem weierstrassZetaExcept_zero (l₀ : ℂ) : weierstrassZetaExcept L l₀ 0 = 0 := by
  simp [weierstrassZetaExcept, zetaTerm_eq]

theorem meromorphic_weierstrassZeta : Meromorphic (weierstrassZeta L) := by
  intro x
  by_cases hx : x ∈ L.lattice
  · have e : weierstrassZeta L =
        fun z => weierstrassZetaExcept L x z + (1 / (z - x) + 1 / x + z / x ^ 2) := by
      ext z; rw [← weierstrassZetaExcept_add L hx, zetaTerm_eq]
    have := (analyticAt_weierstrassZetaExcept L x).meromorphicAt
    rw [e]
    fun_prop
  · exact (analyticOnNhd_weierstrassZeta L x hx).meromorphicAt

theorem tendsto_sub_mul_weierstrassZeta {x : ℂ} (hx : x ∈ L.lattice) :
    Tendsto (fun z => (z - x) * weierstrassZeta L z) (𝓝[≠] x) (𝓝 1) := by
  have hc : ContinuousAt (fun z => (z - x) * (weierstrassZetaExcept L x z + (1 / x + z / x ^ 2)) + 1)
      x := by
    have := (analyticAt_weierstrassZetaExcept L x).continuousAt
    fun_prop
  have h := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := {x}ᶜ))
  simp only [sub_self, zero_mul, zero_add] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with z hz
  have : z - x ≠ 0 := sub_ne_zero.2 hz
  rw [← weierstrassZetaExcept_add L hx, zetaTerm_eq]
  have : (z - x) * (1 / (z - x)) = 1 := by field_simp
  linear_combination -this

def quasiPeriod : ℂ →ₗ[ℝ] ℂ :=
  L.basis.constr ℝ ![2 * weierstrassZeta L (L.ω₁ / 2), 2 * weierstrassZeta L (L.ω₂ / 2)]

theorem quasiPeriod_ω₁ : quasiPeriod L L.ω₁ = 2 * weierstrassZeta L (L.ω₁ / 2) := by
  rw [← L.basis_zero, quasiPeriod, Module.Basis.constr_basis]; simp

theorem quasiPeriod_ω₂ : quasiPeriod L L.ω₂ = 2 * weierstrassZeta L (L.ω₂ / 2) := by
  rw [← L.basis_one, quasiPeriod, Module.Basis.constr_basis]; simp

theorem eqOn_compl_lattice_of_hasDerivAt {f g f' : ℂ → ℂ}
    (hf : ∀ z ∉ L.lattice, HasDerivAt f (f' z) z) (hg : ∀ z ∉ L.lattice, HasDerivAt g (f' z) z)
    {x : ℂ} (hx : x ∉ L.lattice) (h : f x = g x) {z : ℂ} (hz : z ∉ L.lattice) : f z = g z :=
  IsOpen.eqOn_of_deriv_eq (𝕜 := ℂ) L.isClosed_lattice.isOpen_compl (isPreconnected_compl_lattice L)
    (fun z hz => (hf z hz).differentiableAt.differentiableWithinAt)
    (fun z hz => (hg z hz).differentiableAt.differentiableWithinAt)
    (fun z hz => (hf z hz).deriv.trans (hg z hz).deriv.symm) hx h hz

theorem weierstrassZeta_add_of_half_notMem {w : ℂ} (hw : w ∈ L.lattice) (hw2 : w / 2 ∉ L.lattice)
    {z : ℂ} (hz : z ∉ L.lattice) :
    weierstrassZeta L (z + w) = weierstrassZeta L z + 2 * weierstrassZeta L (w / 2) := by
  refine eqOn_compl_lattice_of_hasDerivAt L (f := fun z => weierstrassZeta L (z + w))
    (g := fun z => weierstrassZeta L z + 2 * weierstrassZeta L (w / 2)) (f' := fun z => -℘[L] z)
    (fun z hz => ?_) (fun z hz => (hasDerivAt_weierstrassZeta L hz).add_const _)
    (x := -(w / 2)) (by simpa using hw2) ?_ hz
  · have := (hasDerivAt_weierstrassZeta L (add_notMem_lattice hz hw)).comp_add_const
    rwa [L.weierstrassP_add_coe z ⟨w, hw⟩] at this
  · simp only [weierstrassZeta_neg]
    rw [show -(w / 2) + w = w / 2 by ring]
    ring

theorem weierstrassZeta_add {w : ℂ} (hw : w ∈ L.lattice) {z : ℂ} (hz : z ∉ L.lattice) :
    weierstrassZeta L (z + w) = weierstrassZeta L z + quasiPeriod L w := by
  induction hw using Submodule.span_induction generalizing z with
  | mem x hx =>
    rcases hx with rfl | rfl
    · rw [quasiPeriod_ω₁]
      exact weierstrassZeta_add_of_half_notMem L L.ω₁_mem_lattice L.ω₁_div_two_notMem_lattice hz
    · rw [quasiPeriod_ω₂]
      exact weierstrassZeta_add_of_half_notMem L L.ω₂_mem_lattice L.ω₂_div_two_notMem_lattice hz
  | zero => simp
  | add x y hx hy ihx ihy =>
    rw [← add_assoc, ihy (add_notMem_lattice hz hx), ihx hz, map_add, add_assoc]
  | smul n x hx ih =>
    have hx' : x ∈ L.lattice := hx
    rw [map_zsmul]
    induction n using Int.induction_on generalizing z with
    | zero => simp
    | succ n ihn =>
      rw [add_smul, one_smul, ← add_assoc,
        ih (add_notMem_lattice hz (Submodule.smul_mem _ _ hx')), ihn hz, add_smul, one_smul,
        add_assoc]
    | pred n ihn =>
      have h1 := ih (add_notMem_lattice hz (Submodule.smul_mem _ (-(n : ℤ) - 1) hx'))
      rw [show z + (-(n : ℤ) - 1) • x + x = z + (-(n : ℤ)) • x by module, ihn hz] at h1
      rw [sub_smul (-(n : ℤ)) 1 (quasiPeriod L x), one_smul]
      linear_combination -h1

theorem quasiPeriod_eq_two_mul {w : ℂ} (hw : w ∈ L.lattice) (hw2 : w / 2 ∉ L.lattice) :
    quasiPeriod L w = 2 * weierstrassZeta L (w / 2) := by
  have h1 := weierstrassZeta_add L hw hw2
  rw [weierstrassZeta_add_of_half_notMem L hw hw2 hw2] at h1
  linear_combination -h1

theorem quasiPeriod_eq_weierstrassZetaExcept {w : ℂ} (hw : w ∈ L.lattice) (h0 : w ≠ 0) :
    quasiPeriod L w = weierstrassZetaExcept L w w + 2 / w := by
  have hc : ContinuousAt (fun z => weierstrassZetaExcept L w (z + w) + (1 / w + (z + w) / w ^ 2)
      - weierstrassZetaExcept L 0 z) 0 := by
    have h1 := (analyticAt_weierstrassZetaExcept L 0).continuousAt
    have h2 : ContinuousAt (fun z => weierstrassZetaExcept L w (z + w)) 0 :=
      ContinuousAt.comp_of_eq (analyticAt_weierstrassZetaExcept L w).continuousAt (by fun_prop)
        (zero_add w)
    fun_prop
  have h := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := {0}ᶜ))
  have h' : Tendsto (fun _ : ℂ => quasiPeriod L w) (𝓝[≠] 0) _ := h.congr' (by
    filter_upwards [eventually_notMem_lattice L 0] with z hz
    have h1 := weierstrassZeta_add L hw hz
    rw [← weierstrassZetaExcept_add L hw, zetaTerm_eq, weierstrassZeta_eq_inv_add,
      add_sub_cancel_right] at h1
    linear_combination h1)
  rw [tendsto_nhds_unique tendsto_const_nhds h']
  simp only [zero_add, weierstrassZetaExcept_zero, sub_zero]
  field_simp
  ring

def IsHomothetic (c : ℂ) (L L' : PeriodPair) : Prop := ∀ x, c * x ∈ L'.lattice ↔ x ∈ L.lattice

def scalePeriods (c : ℂ) (hc : c ≠ 0) : PeriodPair where
  ω₁ := c * L.ω₁
  ω₂ := c * L.ω₂
  indep := by
    rw [LinearIndependent.pair_iff]
    intro s t h
    refine LinearIndependent.pair_iff.1 L.indep s t (mul_left_cancel₀ hc ?_)
    simp only [real_smul] at h ⊢
    linear_combination h

theorem isHomothetic_scalePeriods (c : ℂ) (hc : c ≠ 0) :
    IsHomothetic c L (scalePeriods L c hc) := by
  intro x
  simp only [mem_lattice, scalePeriods]
  refine exists₂_congr fun m n => ⟨fun h => mul_left_cancel₀ hc ?_, fun h => ?_⟩
  · linear_combination h
  · linear_combination c * h

theorem isHomothetic_one_iff {L L' : PeriodPair} :
    IsHomothetic 1 L L' ↔ L'.lattice = L.lattice := by
  simp [IsHomothetic, SetLike.ext_iff]

namespace IsHomothetic

variable {L} {L' : PeriodPair} {c : ℂ}

theorem ne_zero (h : IsHomothetic c L L') : c ≠ 0 := by
  rintro rfl
  exact L.ω₁_div_two_notMem_lattice ((h _).1 (by simp))

def equiv (h : IsHomothetic c L L') : L.lattice ≃ L'.lattice where
  toFun x := ⟨c * x, (h _).2 x.2⟩
  invFun y := ⟨c⁻¹ * y, (h _).1 (by simp [h.ne_zero])⟩
  left_inv x := by simp [h.ne_zero]
  right_inv y := by simp [h.ne_zero]

@[simp] theorem coe_equiv (h : IsHomothetic c L L') (x : L.lattice) :
    (h.equiv x : ℂ) = c * x := rfl

theorem weierstrassP_mul (h : IsHomothetic c L L') (z : ℂ) :
    ℘[L'] (c * z) = (c ^ 2)⁻¹ * ℘[L] z := by
  simp only [weierstrassP]
  rw [← h.equiv.tsum_eq, ← tsum_mul_left]
  congr with l
  simp only [coe_equiv, ← mul_sub, mul_pow, one_div, mul_inv]

theorem derivWeierstrassP_mul (h : IsHomothetic c L L') (z : ℂ) :
    ℘'[L'] (c * z) = (c ^ 3)⁻¹ * ℘'[L] z := by
  simp only [derivWeierstrassP]
  rw [← h.equiv.tsum_eq, mul_neg, ← tsum_mul_left]
  congr with l
  simp only [coe_equiv, ← mul_sub, mul_pow, div_eq_mul_inv, mul_inv]
  ring

theorem G_eq (h : IsHomothetic c L L') (n : ℕ) : L'.G n = (c ^ n)⁻¹ * L.G n := by
  simp only [PeriodPair.G]
  rw [← h.equiv.tsum_eq, ← tsum_mul_left]
  simp only [coe_equiv, mul_pow, mul_inv]

theorem weierstrassZeta_mul (h : IsHomothetic c L L') (z : ℂ) :
    weierstrassZeta L' (c * z) = c⁻¹ * weierstrassZeta L z := by
  simp only [weierstrassZeta, zetaTerm_eq]
  rw [← h.equiv.tsum_eq, ← tsum_mul_left]
  congr with l
  have := h.ne_zero
  simp only [coe_equiv, ← mul_sub, mul_pow, div_eq_mul_inv, mul_inv]
  field_simp

theorem quasiPeriod_mul (h : IsHomothetic c L L') (w : ℂ) :
    quasiPeriod L' (c * w) = c⁻¹ * quasiPeriod L w := by
  have key : ∀ w ∈ L.lattice, quasiPeriod L' (c * w) = c⁻¹ * quasiPeriod L w := by
    intro w hw
    have hz := L.ω₁_div_two_notMem_lattice
    have h1 := weierstrassZeta_add L' ((h w).2 hw) ((h _).not.2 hz)
    rw [← mul_add, h.weierstrassZeta_mul, h.weierstrassZeta_mul, weierstrassZeta_add L hw hz] at h1
    linear_combination -h1
  have : (quasiPeriod L').comp (LinearMap.mulLeft ℝ c) =
      (LinearMap.mulLeft ℝ c⁻¹).comp (quasiPeriod L) := by
    refine L.basis.ext fun i => ?_
    fin_cases i
    · simpa using key _ L.ω₁_mem_lattice
    · simpa using key _ L.ω₂_mem_lattice
  exact LinearMap.congr_fun this w

end IsHomothetic

theorem weierstrassZeta_congr {L L' : PeriodPair} (h : L'.lattice = L.lattice) :
    weierstrassZeta L' = weierstrassZeta L := by
  ext z; simpa using (isHomothetic_one_iff.2 h).weierstrassZeta_mul z

theorem quasiPeriod_congr {L L' : PeriodPair} (h : L'.lattice = L.lattice) :
    quasiPeriod L' = quasiPeriod L :=
  LinearMap.ext fun z => by simpa using (isHomothetic_one_iff.2 h).quasiPeriod_mul z

open EisensteinSeries SummationFilter in

theorem quasiPeriod_ω₁_eq_eisenstein (τ : UpperHalfPlane) (hτ : (τ : ℂ) * L.ω₁ = L.ω₂) :
    quasiPeriod L L.ω₁ = L.ω₁⁻¹ * G2 τ := by
  have h0 : L.ω₁ ≠ 0 := by simpa using L.indep.ne_zero 0
  have h1 : quasiPeriod L L.ω₁ = weierstrassZeta L L.ω₁ := by
    rw [quasiPeriod_eq_weierstrassZetaExcept L L.ω₁_mem_lattice h0,
      ← weierstrassZetaExcept_add L L.ω₁_mem_lattice, zetaTerm_eq]
    simp only [sub_self, div_zero, zero_add]
    field_simp
    ring
  let e : ℤ × ℤ ≃ L.lattice :=
    ((Equiv.prodComm ℤ ℤ).trans L.latticeEquivProd.symm.toEquiv).trans (Equiv.neg _)
  have he : ∀ p : ℤ × ℤ, (e p : ℂ) = -(L.ω₁ * (p.1 * τ + p.2)) := by
    intro p
    have := L.latticeEquiv_symm_apply p.swap
    simp only [Prod.fst_swap, Prod.snd_swap] at this
    simp only [e, Equiv.trans_apply, Equiv.prodComm_apply, Equiv.neg_apply, NegMemClass.coe_neg,
      LinearEquiv.coe_toEquiv, this, ← hτ]
    ring
  have h2 := (e.hasSum_iff.2 (hasSum_weierstrassZeta L L.ω₁))
  have h3 : HasSum (fun m : ℤ => L.ω₁⁻¹ * e2Summand m τ) (weierstrassZeta L L.ω₁) := by
    refine h2.prod_fiberwise fun m => ?_
    have s1 := (e2Summand_summable m τ).hasSum
    have s2 := (summable_right_one_div_linear_sub_one_div_linear_succ τ m).hasSum
    rw [← tsum_eq_of_summable_unconditional (L := symmetricIco ℤ)
      (summable_right_one_div_linear_sub_one_div_linear_succ τ m),
      tsum_symmetricIco_linear_sub_linear_add_one_eq_zero] at s2
    convert (s1.sub s2).mul_left L.ω₁⁻¹ using 1
    · rfl
    · ext n
      simp only [Function.comp_apply, he, zetaTerm_eq, eisSummand, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_fin_one]
      rw [show L.ω₁ - -(L.ω₁ * (m * τ + n)) = L.ω₁ * (m * τ + n + 1) by ring]
      simp only [zpow_neg, zpow_ofNat, div_neg, inv_neg, neg_sq, mul_pow, div_eq_mul_inv, mul_inv, one_mul]
      generalize ((m : ℂ) * τ + n + 1)⁻¹ = a
      generalize (((m : ℂ) * τ + n) ^ 2)⁻¹ = b
      linear_combination (L.ω₁⁻¹ * b) * mul_inv_cancel₀ h0
    · rw [sub_zero, e2Summand]
  have h4 := h3.mul_left L.ω₁
  simp only [mul_inv_cancel_left₀ h0] at h4
  rw [h1, G2, tsum_eq_of_summable_unconditional h4.summable, h4.tsum_eq, inv_mul_cancel_left₀ h0]

def rotatePeriods : PeriodPair where
  ω₁ := L.ω₂
  ω₂ := -L.ω₁
  indep := by
    rw [LinearIndependent.pair_iff]
    intro s t h
    have := LinearIndependent.pair_iff.1 L.indep (-t) s (by
      simp only [real_smul, ofReal_neg] at h ⊢
      linear_combination h)
    exact ⟨this.2, by simpa using this.1⟩

theorem lattice_rotatePeriods : (rotatePeriods L).lattice = L.lattice := by
  ext x
  simp only [mem_lattice, rotatePeriods]
  constructor
  · rintro ⟨m, n, h⟩
    exact ⟨-n, m, by push_cast; linear_combination h⟩
  · rintro ⟨m, n, h⟩
    exact ⟨n, -m, by push_cast; linear_combination h⟩

def swapPeriods : PeriodPair where
  ω₁ := L.ω₂
  ω₂ := L.ω₁
  indep := LinearIndependent.pair_symm_iff.1 L.indep

theorem lattice_swapPeriods : (swapPeriods L).lattice = L.lattice := by
  simp only [lattice, swapPeriods, Set.pair_comm]

theorem legendre_relation (h : 0 < (L.ω₂ / L.ω₁).im) :
    quasiPeriod L L.ω₁ * L.ω₂ - quasiPeriod L L.ω₂ * L.ω₁ = 2 * π * I := by
  have h1 : L.ω₁ ≠ 0 := by simpa using L.indep.ne_zero 0
  have h2 : L.ω₂ ≠ 0 := by simpa using L.indep.ne_zero 1
  let τ : UpperHalfPlane := ⟨L.ω₂ / L.ω₁, h⟩
  have hτ : (τ : ℂ) = L.ω₂ / L.ω₁ := rfl
  have hS : ((ModularGroup.S • τ : UpperHalfPlane) : ℂ) = -(L.ω₁ / L.ω₂) := by
    rw [UpperHalfPlane.modular_S_smul]
    simp [hτ]
  have e1 := quasiPeriod_ω₁_eq_eisenstein L τ (by rw [hτ]; field_simp)
  have e2 := quasiPeriod_ω₁_eq_eisenstein (rotatePeriods L) (ModularGroup.S • τ)
    (by rw [hS]; simp only [rotatePeriods]; field_simp)
  rw [quasiPeriod_congr (lattice_rotatePeriods L)] at e2
  simp only [rotatePeriods] at e2
  rw [e1, e2, EisensteinSeries.G2_S_transform τ, hτ]
  field_simp
  ring

def latticeArea : ℝ := ZLattice.covolume L.lattice

theorem latticeArea_pos : 0 < latticeArea L := ZLattice.covolume_pos _ _

theorem latticeArea_eq : latticeArea L = |(conj L.ω₁ * L.ω₂).im| := by
  rw [latticeArea, ZLattice.covolume_eq_det_mul_measureReal _ _ L.latticeBasis
    Complex.orthonormalBasisOneI.toBasis,
    MeasureTheory.measureReal_congr (ZSpan.fundamentalDomain_ae_parallelepiped _ _),
    MeasureTheory.Measure.real, OrthonormalBasis.coe_toBasis,
    Complex.orthonormalBasisOneI.volume_parallelepiped]
  simp only [ENNReal.toReal_one, mul_one]
  congr 1
  rw [Module.Basis.det_apply, Matrix.det_fin_two]
  simp [Module.Basis.toMatrix_apply]
  ring

theorem latticeArea_congr {L L' : PeriodPair} (h : L'.lattice = L.lattice) :
    latticeArea L' = latticeArea L := by
  simp only [latticeArea, h]

theorem IsHomothetic.latticeArea_eq {L L' : PeriodPair} {c : ℂ} (h : IsHomothetic c L L') :
    latticeArea L' = ‖c‖ ^ 2 * latticeArea L := by
  have e : L'.lattice = (scalePeriods L c h.ne_zero).lattice := by
    ext x
    have h1 := h (c⁻¹ * x)
    have h2 := isHomothetic_scalePeriods L c h.ne_zero (c⁻¹ * x)
    rw [mul_inv_cancel_left₀ h.ne_zero] at h1 h2
    exact h1.trans h2.symm
  rw [latticeArea_congr e, GlobalTheory.latticeArea_eq, GlobalTheory.latticeArea_eq, ← abs_of_nonneg
    (sq_nonneg ‖c‖), ← abs_mul, Complex.sq_norm, Complex.normSq_apply]
  congr 1
  simp [scalePeriods]
  ring

def sTwo : ℂ := (quasiPeriod L 1 - I * quasiPeriod L I) / 2

theorem realLinear_eq_add_conj (f : ℂ →ₗ[ℝ] ℂ) (w : ℂ) :
    f w = (f 1 - I * f I) / 2 * w + (f 1 + I * f I) / 2 * conj w := by
  have : f w = w.re * f 1 + w.im * f I := by
    conv_lhs => rw [show w = w.re • (1 : ℂ) + w.im • I by simp]
    rw [map_add, map_smul, map_smul, real_smul, real_smul]
  rw [this]
  have h1 : conj w = w.re - w.im * I := by apply Complex.ext <;> simp
  rw [h1]
  conv_rhs => enter [1, 2]; rw [← re_add_im w]
  linear_combination (w.im * f I) * I_mul_I

theorem quasiPeriod_eq (w : ℂ) :
    quasiPeriod L w = sTwo L * w + (π / latticeArea L : ℝ) * conj w := by
  wlog h : 0 < (L.ω₂ / L.ω₁).im generalizing L
  · have h1 : L.ω₁ ≠ 0 := by simpa using L.indep.ne_zero 0
    have h2 : L.ω₂ ≠ 0 := by simpa using L.indep.ne_zero 1
    have hA := latticeArea_pos L
    rw [latticeArea_eq, abs_pos] at hA
    have := this (swapPeriods L) (by
      simp only [swapPeriods]
      have n1 := normSq_pos.2 h1
      have n2 := normSq_pos.2 h2
      rw [div_im, ← sub_div] at h ⊢
      rw [not_lt, div_nonpos_iff] at h
      simp only [mul_im, conj_re, conj_im] at hA
      refine div_pos (lt_of_le_of_ne ?_ fun h' => hA ?_) n2
      · rcases h with h | h <;> nlinarith [h.1, h.2]
      · linarith)
    rwa [sTwo, quasiPeriod_congr (lattice_swapPeriods L),
      latticeArea_congr (lattice_swapPeriods L)] at this
  have h1 : L.ω₁ ≠ 0 := by simpa using L.indep.ne_zero 0
  have hleg := legendre_relation L h
  have hA : latticeArea L = (conj L.ω₁ * L.ω₂).im := by
    rw [latticeArea_eq, abs_of_pos]
    rw [div_im, ← sub_div, div_pos_iff_of_pos_right (normSq_pos.2 h1)] at h
    simp only [mul_im, conj_re, conj_im]
    linarith
  have hA' : conj L.ω₁ * L.ω₂ - conj L.ω₂ * L.ω₁ = 2 * (latticeArea L : ℂ) * I := by
    rw [hA]; apply Complex.ext <;> simp <;> ring
  have hA0 : (latticeArea L : ℂ) ≠ 0 := by exact_mod_cast (latticeArea_pos L).ne'
  have hc : (quasiPeriod L 1 + I * quasiPeriod L I) / 2 = (π / latticeArea L : ℝ) := by
    rw [realLinear_eq_add_conj _ L.ω₁, realLinear_eq_add_conj _ L.ω₂] at hleg
    push_cast
    rw [eq_div_iff hA0]
    refine mul_right_cancel₀ (mul_ne_zero two_ne_zero I_ne_zero) ?_
    linear_combination hleg - (quasiPeriod L 1 + I * quasiPeriod L I) / 2 * hA'
  rw [realLinear_eq_add_conj, hc, sTwo]

theorem sTwo_unique {s w : ℂ} (hw : w ≠ 0)
    (h : quasiPeriod L w = s * w + (π / latticeArea L : ℝ) * conj w) : s = sTwo L := by
  rw [quasiPeriod_eq] at h
  exact (mul_right_cancel₀ hw (add_right_cancel h)).symm

theorem quasiPeriod_mul_sub (a b : ℂ) : quasiPeriod L a * b - quasiPeriod L b * a =
    2 * π * I * ((conj a * b).im / latticeArea L : ℝ) := by
  have : conj a * b - conj b * a = 2 * ((conj a * b).im : ℂ) * I := by
    apply Complex.ext <;> simp <;> ring
  rw [quasiPeriod_eq, quasiPeriod_eq]
  push_cast
  linear_combination (π / latticeArea L : ℂ) * this

theorem IsHomothetic.sTwo_eq {L L' : PeriodPair} {c : ℂ} (h : IsHomothetic c L L') :
    sTwo L' = (c ^ 2)⁻¹ * sTwo L := by
  have hc := h.ne_zero
  refine (sTwo_unique L' hc ?_).symm
  have h1 := h.quasiPeriod_mul 1
  have hA0 : (latticeArea L : ℂ) ≠ 0 := by exact_mod_cast (latticeArea_pos L).ne'
  have hc' : conj c ≠ 0 := by simpa using hc
  rw [mul_one] at h1
  rw [h1, quasiPeriod_eq, h.latticeArea_eq]
  push_cast
  rw [← mul_conj']
  simp only [map_one]
  field_simp

theorem sTwo_congr {L L' : PeriodPair} (h : L'.lattice = L.lattice) : sTwo L' = sTwo L := by
  simp only [sTwo, quasiPeriod_congr h]

theorem sTwo_eq_eisenstein (τ : UpperHalfPlane) (h1 : L.ω₁ = 1) (h2 : L.ω₂ = τ) :
    sTwo L = EisensteinSeries.G2 τ - (π / τ.im : ℝ) := by
  have e := quasiPeriod_ω₁_eq_eisenstein L τ (by rw [h1, h2, mul_one])
  have hA : latticeArea L = τ.im := by
    rw [latticeArea_eq, h1, h2]; simp [abs_of_pos τ.im_pos]
  rw [quasiPeriod_eq, h1, hA] at e
  simp only [mul_one, map_one, inv_one, one_mul] at e
  linear_combination e

def primaryFactor (w : ℂ) : ℂ := (1 - w) * cexp (w + w ^ 2 / 2)

@[simp] theorem primaryFactor_zero : primaryFactor 0 = 1 := by simp [primaryFactor]

theorem primaryFactor_eq_zero_iff {w : ℂ} : primaryFactor w = 0 ↔ w = 1 := by
  rw [primaryFactor, mul_eq_zero, or_iff_left (exp_ne_zero _), sub_eq_zero, eq_comm]

@[fun_prop] theorem differentiable_primaryFactor : Differentiable ℂ primaryFactor := by
  unfold primaryFactor; fun_prop

theorem norm_primaryFactor_sub_one_le {w : ℂ} (hw : ‖w‖ ≤ 1 / 2) :
    ‖primaryFactor w - 1‖ ≤ 2 * ‖w‖ ^ 3 := by
  have h1 : 1 - w ≠ 0 := by
    intro h
    rw [← sub_eq_zero.1 h] at hw
    norm_num at hw
  have h2 := norm_log_sub_logTaylor_le 2 (z := -w) (by rw [norm_neg]; linarith)
  have h3 : logTaylor (2 + 1) (-w) = -(w + w ^ 2 / 2) := by
    simp [logTaylor, Finset.sum_range_succ]; ring
  rw [h3, norm_neg, ← sub_eq_add_neg, sub_neg_eq_add] at h2
  have h4 : (1 - ‖w‖)⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
  have h0 := norm_nonneg w
  have h5 : ‖log (1 - w) + (w + w ^ 2 / 2)‖ ≤ ‖w‖ ^ 3 := by
    refine h2.trans ?_
    have : 0 ≤ ‖w‖ ^ 3 := by positivity
    push_cast
    nlinarith
  have h6 : ‖w‖ ^ 3 ≤ 1 := pow_le_one₀ h0 (by linarith)
  rw [primaryFactor, ← exp_log h1, ← Complex.exp_add]
  exact (norm_exp_sub_one_le (h5.trans h6)).trans (by linarith)

def sigmaFactor (l z : ℂ) : ℂ := if l = 0 then 1 else primaryFactor (z / l)

theorem sigmaFactor_eq (l z : ℂ) : sigmaFactor l z = primaryFactor (z / l) := by
  unfold sigmaFactor
  split_ifs with h
  · simp [h]
  · rfl

theorem differentiable_sigmaFactor (l : ℂ) : Differentiable ℂ (sigmaFactor l) := by
  have : sigmaFactor l = fun z => primaryFactor (z / l) := funext (sigmaFactor_eq l)
  rw [this]; fun_prop

theorem sigmaFactor_eq_zero_iff {l z : ℂ} : sigmaFactor l z = 0 ↔ l ≠ 0 ∧ z = l := by
  unfold sigmaFactor
  split_ifs with h
  · simp [h]
  · simp [h, primaryFactor_eq_zero_iff, div_eq_one_iff_eq h]

theorem norm_sigmaFactor_sub_one_le {r : ℝ} (hr : 0 < r) {z : ℂ} (hz : ‖z‖ ≤ r) {l : ℂ}
    (h : 2 * r ≤ ‖l‖) : ‖sigmaFactor l z - 1‖ ≤ 2 * r ^ 3 * ‖l‖ ^ (-3 : ℝ) := by
  have hl : 0 < ‖l‖ := by linarith
  rw [sigmaFactor_eq]
  refine (norm_primaryFactor_sub_one_le ?_).trans ?_
  · rw [norm_div, div_le_iff₀ hl]; linarith
  · calc 2 * ‖z / l‖ ^ 3 = 2 * ‖z‖ ^ 3 / ‖l‖ ^ 3 := by rw [norm_div]; ring
      _ ≤ 2 * r ^ 3 / ‖l‖ ^ 3 := by gcongr
      _ = _ := by norm_cast

theorem logDeriv_sigmaFactor {l z : ℂ} (h : sigmaFactor l z ≠ 0) :
    logDeriv (sigmaFactor l) z = if l = 0 then 0 else zetaTerm l z := by
  split_ifs with hl
  · have : sigmaFactor l = fun _ => 1 := by ext; simp [sigmaFactor, hl]
    simp [this]
  have hz : z - l ≠ 0 := fun h' => h (sigmaFactor_eq_zero_iff.2 ⟨hl, sub_eq_zero.1 h'⟩)
  have e : sigmaFactor l = fun z => (1 - z / l) * cexp (z / l + (z / l) ^ 2 / 2) :=
    funext (sigmaFactor_eq l)
  have h1 := (hasDerivAt_id' z).div_const l
  have h2 := ((h1.const_sub 1).fun_mul (h1.fun_add ((h1.fun_pow 2).div_const 2)).cexp).deriv
  have hz' : l - z ≠ 0 := fun h' => hz (by linear_combination -h')
  rw [logDeriv_apply, e, h2, zetaTerm_eq, show z - l = -(l - z) by ring]
  beta_reduce
  have := exp_ne_zero (z / l + (z / l) ^ 2 / 2)
  generalize cexp (z / l + (z / l) ^ 2 / 2) = E at *
  simp only [Nat.cast_ofNat, Nat.add_one_sub_one, pow_one]
  field_simp
  ring

def sigmaProd (z : ℂ) : ℂ := ∏' l : L.lattice, sigmaFactor l z

def weierstrassSigma (z : ℂ) : ℂ := z * sigmaProd L z

theorem hasProdLocallyUniformlyOn_sigmaProd :
    HasProdLocallyUniformlyOn (fun (l : L.lattice) z => sigmaFactor l z) (sigmaProd L)
      Set.univ := by
  refine hasProdLocallyUniformlyOn_of_forall_compact isOpen_univ fun K _ hK => ?_
  obtain ⟨r, hr, hKr⟩ := hK.isBounded.exists_pos_norm_le
  have := Summable.hasProdUniformlyOn_one_add (f := fun (l : L.lattice) z => sigmaFactor l z - 1)
    (u := fun l => 2 * r ^ 3 * ‖l‖ ^ (-3 : ℝ)) hK
    ((ZLattice.summable_norm_rpow _ _ (by simp; norm_num)).mul_left _)
    ((eventually_cofinite_le_norm L (2 * r)).mono fun l hl z hz =>
      norm_sigmaFactor_sub_one_le hr (hKr z hz) hl)
    (fun l => ((differentiable_sigmaFactor l).continuous.sub continuous_const).continuousOn)
  simpa only [add_sub_cancel] using! this

theorem hasProd_sigmaProd (z : ℂ) :
    HasProd (fun l : L.lattice => sigmaFactor l z) (sigmaProd L z) :=
  (hasProdLocallyUniformlyOn_sigmaProd L).hasProd (Set.mem_univ z)

theorem summable_norm_sigmaFactor_sub_one (z : ℂ) :
    Summable fun l : L.lattice => ‖sigmaFactor l z - 1‖ := by
  refine Summable.of_norm_bounded_eventually
    (g := fun l : L.lattice => 2 * (‖z‖ + 1) ^ 3 * ‖l‖ ^ (-3 : ℝ))
    ((ZLattice.summable_norm_rpow _ _ (by simp; norm_num)).mul_left _) ?_
  filter_upwards [eventually_cofinite_le_norm L (2 * (‖z‖ + 1))] with l hl
  rw [norm_norm]
  exact norm_sigmaFactor_sub_one_le (by positivity) (by linarith) hl

@[fun_prop] theorem differentiable_sigmaProd : Differentiable ℂ (sigmaProd L) :=
  differentiableOn_univ.1 <| TendstoLocallyUniformlyOn.differentiableOn
    (hasProdLocallyUniformlyOn_sigmaProd L)
    (.of_forall fun _ => DifferentiableOn.fun_finset_prod fun l _ =>
      (differentiable_sigmaFactor l).differentiableOn) isOpen_univ

@[simp] theorem sigmaProd_zero : sigmaProd L 0 = 1 := by simp [sigmaProd, sigmaFactor_eq]

@[simp] theorem sigmaProd_neg (z : ℂ) : sigmaProd L (-z) = sigmaProd L z := by
  simp only [sigmaProd, sigmaFactor_eq]
  rw [← (Equiv.neg L.lattice).tprod_eq]
  simp

theorem sigmaProd_ne_zero {z : ℂ} (hz : z ∈ ((L.lattice : Set ℂ) \ {0})ᶜ) : sigmaProd L z ≠ 0 := by
  have := tprod_one_add_ne_zero_of_summable (f := fun l : L.lattice => sigmaFactor l z - 1)
    (fun l => by
      rw [add_sub_cancel, Ne, sigmaFactor_eq_zero_iff]
      rintro ⟨h0, rfl⟩
      exact hz ⟨l.2, h0⟩) (summable_norm_sigmaFactor_sub_one L z)
  simpa only [add_sub_cancel] using! this

theorem logDeriv_sigmaProd {z : ℂ} (hz : z ∈ ((L.lattice : Set ℂ) \ {0})ᶜ) :
    logDeriv (sigmaProd L) z = weierstrassZetaExcept L 0 z := by
  have hne : ∀ l : L.lattice, sigmaFactor l z ≠ 0 := fun l => by
    rw [Ne, sigmaFactor_eq_zero_iff]
    rintro ⟨h0, rfl⟩
    exact hz ⟨l.2, h0⟩
  have := logDeriv_tprod_eq_tsum (f := fun (l : L.lattice) z => sigmaFactor l z) isOpen_univ
    (Set.mem_univ z) hne (fun l => (differentiable_sigmaFactor l).differentiableOn)
    ((hasSum_weierstrassZetaExcept L 0 z).summable.congr fun l =>
      (logDeriv_sigmaFactor (hne l)).symm)
    (hasProdLocallyUniformlyOn_sigmaProd L).multipliableLocallyUniformlyOn
    (sigmaProd_ne_zero L hz)
  exact this.trans (tsum_congr fun l => logDeriv_sigmaFactor (hne l))

@[fun_prop] theorem differentiable_weierstrassSigma : Differentiable ℂ (weierstrassSigma L) := by
  unfold weierstrassSigma; fun_prop

@[fun_prop] theorem analyticAt_weierstrassSigma (z : ℂ) : AnalyticAt ℂ (weierstrassSigma L) z :=
  (differentiable_weierstrassSigma L).analyticAt z

@[fun_prop] theorem continuous_weierstrassSigma : Continuous (weierstrassSigma L) :=
  (differentiable_weierstrassSigma L).continuous

@[simp] theorem weierstrassSigma_zero : weierstrassSigma L 0 = 0 := by simp [weierstrassSigma]

@[simp] theorem weierstrassSigma_neg (z : ℂ) :
    weierstrassSigma L (-z) = -weierstrassSigma L z := by simp [weierstrassSigma]

theorem hasDerivAt_weierstrassSigma_zero : HasDerivAt (weierstrassSigma L) 1 0 :=
  ((hasDerivAt_id' (0 : ℂ)).fun_mul (differentiable_sigmaProd L 0).hasDerivAt).congr_deriv (by simp)

theorem weierstrassSigma_ne_zero {z : ℂ} (hz : z ∉ L.lattice) : weierstrassSigma L z ≠ 0 :=
  mul_ne_zero (fun h => hz (h ▸ zero_mem _)) (sigmaProd_ne_zero L fun h => hz h.1)

theorem hasDerivAt_weierstrassSigma {z : ℂ} (hz : z ∉ L.lattice) :
    HasDerivAt (weierstrassSigma L) (weierstrassZeta L z * weierstrassSigma L z) z := by
  refine ((hasDerivAt_id' z).fun_mul (differentiable_sigmaProd L z).hasDerivAt).congr_deriv ?_
  have h0 : z ≠ 0 := fun h => hz (h ▸ zero_mem _)
  have h1 := sigmaProd_ne_zero L (z := z) fun h => hz h.1
  rw [weierstrassZeta_eq_inv_add, ← logDeriv_sigmaProd L fun h => hz h.1, logDeriv_apply,
    weierstrassSigma]
  field_simp

theorem logDeriv_weierstrassSigma {z : ℂ} (hz : z ∉ L.lattice) :
    logDeriv (weierstrassSigma L) z = weierstrassZeta L z := by
  rw [logDeriv_apply, (hasDerivAt_weierstrassSigma L hz).deriv,
    mul_div_cancel_right₀ _ (weierstrassSigma_ne_zero L hz)]

theorem IsHomothetic.sigmaProd_mul {L L' : PeriodPair} {c : ℂ} (h : IsHomothetic c L L') (z : ℂ) :
    sigmaProd L' (c * z) = sigmaProd L z := by
  simp only [sigmaProd, sigmaFactor_eq]
  rw [← h.equiv.tprod_eq]
  simp only [IsHomothetic.coe_equiv, mul_div_mul_left _ _ h.ne_zero]

theorem IsHomothetic.weierstrassSigma_mul {L L' : PeriodPair} {c : ℂ} (h : IsHomothetic c L L')
    (z : ℂ) : weierstrassSigma L' (c * z) = c * weierstrassSigma L z := by
  rw [weierstrassSigma, h.sigmaProd_mul, weierstrassSigma, mul_assoc]

theorem weierstrassSigma_congr {L L' : PeriodPair} (h : L'.lattice = L.lattice) :
    weierstrassSigma L' = weierstrassSigma L := by
  ext z; simpa using (isHomothetic_one_iff.2 h).weierstrassSigma_mul z

open Classical in

def sigmaSign (w : ℂ) : ℂ := if w / 2 ∈ L.lattice then 1 else -1

theorem sigmaSign_of_mem {w : ℂ} (h : w / 2 ∈ L.lattice) : sigmaSign L w = 1 := if_pos h

theorem sigmaSign_of_notMem {w : ℂ} (h : w / 2 ∉ L.lattice) : sigmaSign L w = -1 := if_neg h

@[simp] theorem sigmaSign_sq (w : ℂ) : sigmaSign L w ^ 2 = 1 := by
  unfold sigmaSign; split_ifs <;> simp

@[simp] theorem norm_sigmaSign (w : ℂ) : ‖sigmaSign L w‖ = 1 := by
  unfold sigmaSign; split_ifs <;> simp

theorem sigmaSign_ne_zero (w : ℂ) : sigmaSign L w ≠ 0 := by
  unfold sigmaSign; split_ifs <;> simp

def sigmaSignCircle (w : ℂ) : Circle := ⟨sigmaSign L w, by simp [Submonoid.unitSphere]⟩

@[simp] theorem coe_sigmaSignCircle (w : ℂ) : (sigmaSignCircle L w : ℂ) = sigmaSign L w := rfl

@[simp] theorem sigmaSign_zero : sigmaSign L 0 = 1 := sigmaSign_of_mem L (by simp)

@[simp] theorem sigmaSign_neg (w : ℂ) : sigmaSign L (-w) = sigmaSign L w := by
  classical
  unfold sigmaSign
  exact if_congr (by rw [neg_div, neg_mem_iff]) rfl rfl

theorem IsHomothetic.sigmaSign_mul {L L' : PeriodPair} {c : ℂ} (h : IsHomothetic c L L') (w : ℂ) :
    sigmaSign L' (c * w) = sigmaSign L w := by
  classical
  unfold sigmaSign
  exact if_congr (by rw [mul_div_assoc, h (w / 2)]) rfl rfl

theorem sigmaSign_int (m n : ℤ) : sigmaSign L (m * L.ω₁ + n * L.ω₂) = (-1) ^ (m + n + m * n) := by
  have h : (m * L.ω₁ + n * L.ω₂) / 2 ∈ L.lattice ↔ Even m ∧ Even n := by
    constructor
    · intro h
      obtain ⟨a, b, e⟩ := mem_lattice.1 h
      have := LinearIndependent.pair_iff.1 L.indep (m - 2 * a) (n - 2 * b) (by
        simp only [real_smul]; push_cast; linear_combination (-2) * e)
      simp only [sub_eq_zero] at this
      norm_cast at this
      exact ⟨⟨a, by omega⟩, ⟨b, by omega⟩⟩
    · rintro ⟨⟨a, rfl⟩, ⟨b, rfl⟩⟩
      exact mem_lattice.2 ⟨a, b, by push_cast; ring⟩
  by_cases h' : Even m ∧ Even n
  · rw [sigmaSign_of_mem L (h.2 h'), Even.neg_one_zpow ((h'.1.add h'.2).add (h'.1.mul_right _))]
  · rw [sigmaSign_of_notMem L (h.not.2 h'), Odd.neg_one_zpow]
    rw [← Int.not_even_iff_odd]
    simp only [Int.even_add, Int.even_mul]
    tauto

theorem exists_weierstrassSigma_add {w : ℂ} (hw : w ∈ L.lattice) : ∃ C : ℂ, C ≠ 0 ∧ ∀ z,
    weierstrassSigma L (z + w) = C * cexp (quasiPeriod L w * (z + w / 2)) * weierstrassSigma L z := by
  set x := L.ω₁ / 2
  have hx : x ∉ L.lattice := L.ω₁_div_two_notMem_lattice
  let g : ℂ → ℂ := fun z =>
    weierstrassSigma L (z + w) / (cexp (quasiPeriod L w * (z + w / 2)) * weierstrassSigma L z)
  have hg : ∀ z ∉ L.lattice, HasDerivAt g 0 z := by
    intro z hz
    have h1 := (hasDerivAt_weierstrassSigma L (add_notMem_lattice hz hw)).comp_add_const
    have h2 := (((hasDerivAt_id' z).add_const (w / 2)).const_mul (quasiPeriod L w)).cexp
    refine (h1.fun_div (h2.fun_mul (hasDerivAt_weierstrassSigma L hz))
      (mul_ne_zero (exp_ne_zero _) (weierstrassSigma_ne_zero L hz))).congr_deriv ?_
    rw [weierstrassZeta_add L hw hz, div_eq_zero_iff]
    left
    ring
  refine ⟨g x, div_ne_zero (weierstrassSigma_ne_zero L (add_notMem_lattice hx hw))
    (mul_ne_zero (exp_ne_zero _) (weierstrassSigma_ne_zero L hx)), fun z => ?_⟩
  refine congrFun (Continuous.ext_on (dense_compl_lattice L)
    (f := fun z => weierstrassSigma L (z + w))
    (g := fun z => g x * cexp (quasiPeriod L w * (z + w / 2)) * weierstrassSigma L z)
    (by fun_prop) (by fun_prop) fun z hz => ?_) z
  have := eqOn_compl_lattice_of_hasDerivAt L hg (fun z _ => hasDerivAt_const z (g x)) hx rfl hz
  beta_reduce
  rw [← this, mul_assoc, div_mul_cancel₀ _
    (mul_ne_zero (exp_ne_zero _) (weierstrassSigma_ne_zero L hz))]

theorem weierstrassSigma_eq_zero_iff {z : ℂ} : weierstrassSigma L z = 0 ↔ z ∈ L.lattice := by
  refine ⟨fun h => by_contra fun hz => weierstrassSigma_ne_zero L hz h, fun hz => ?_⟩
  obtain ⟨C, -, h⟩ := exists_weierstrassSigma_add L hz
  simpa using h 0

theorem deriv_weierstrassSigma_add_of_law {w C η x : ℂ}
    (h : ∀ z, weierstrassSigma L (z + w) = C * cexp (η * (z + w / 2)) * weierstrassSigma L z)
    (hx : weierstrassSigma L x = 0) : deriv (weierstrassSigma L) (x + w) =
      C * cexp (η * (x + w / 2)) * deriv (weierstrassSigma L) x := by
  have h1 := (differentiable_weierstrassSigma L (x + w)).hasDerivAt.comp_add_const
  have h2 := (((((hasDerivAt_id' x).add_const (w / 2)).const_mul η).cexp).const_mul C).fun_mul
    (differentiable_weierstrassSigma L x).hasDerivAt
  rw [funext h] at h1
  simpa [hx] using h1.unique h2

theorem deriv_weierstrassSigma_ne_zero {w : ℂ} (hw : w ∈ L.lattice) :
    deriv (weierstrassSigma L) w ≠ 0 := by
  obtain ⟨C, hC, h⟩ := exists_weierstrassSigma_add L hw
  have := deriv_weierstrassSigma_add_of_law L h (weierstrassSigma_zero L)
  rw [zero_add, (hasDerivAt_weierstrassSigma_zero L).deriv, mul_one] at this
  rw [this]
  exact mul_ne_zero hC (exp_ne_zero _)

theorem deriv_weierstrassSigma_neg (z : ℂ) :
    deriv (weierstrassSigma L) (-z) = deriv (weierstrassSigma L) z := by
  have h := deriv_comp_neg (weierstrassSigma L) z
  simp only [weierstrassSigma_neg, deriv.fun_neg', neg_inj] at h
  exact h.symm

theorem weierstrassSigma_add {w : ℂ} (hw : w ∈ L.lattice) (z : ℂ) :
    weierstrassSigma L (z + w) =
      sigmaSign L w * cexp (quasiPeriod L w * (z + w / 2)) * weierstrassSigma L z := by
  obtain ⟨C, -, h⟩ := exists_weierstrassSigma_add L hw
  have e : -(w / 2) + w = w / 2 := by ring
  suffices C = sigmaSign L w by rw [h, this]
  by_cases h2 : w / 2 ∈ L.lattice
  · have := deriv_weierstrassSigma_add_of_law L h
      ((weierstrassSigma_eq_zero_iff L).2 (neg_mem h2))
    rw [e, deriv_weierstrassSigma_neg, neg_add_cancel, mul_zero, Complex.exp_zero, mul_one] at this
    rw [sigmaSign_of_mem L h2]
    exact mul_right_cancel₀ (deriv_weierstrassSigma_ne_zero L h2) (by linear_combination -this)
  · have := h (-(w / 2))
    rw [e, weierstrassSigma_neg, neg_add_cancel, mul_zero, Complex.exp_zero, mul_one] at this
    rw [sigmaSign_of_notMem L h2]
    exact mul_right_cancel₀ (weierstrassSigma_ne_zero L h2) (by linear_combination this)

theorem deriv_weierstrassSigma_of_mem {w : ℂ} (hw : w ∈ L.lattice) :
    deriv (weierstrassSigma L) w = sigmaSign L w * cexp (quasiPeriod L w * (w / 2)) := by
  simpa [(hasDerivAt_weierstrassSigma_zero L).deriv] using
    deriv_weierstrassSigma_add_of_law L (weierstrassSigma_add L hw) (weierstrassSigma_zero L)

theorem analyticOrderAt_weierstrassSigma_of_mem {w : ℂ} (hw : w ∈ L.lattice) :
    analyticOrderAt (weierstrassSigma L) w = 1 :=
  (analyticAt_weierstrassSigma L w).analyticOrderAt_eq_one_of_zero_deriv_ne_zero
    ((weierstrassSigma_eq_zero_iff L).2 hw) (deriv_weierstrassSigma_ne_zero L hw)

theorem analyticOrderAt_weierstrassSigma_of_notMem {z : ℂ} (hz : z ∉ L.lattice) :
    analyticOrderAt (weierstrassSigma L) z = 0 :=
  (analyticAt_weierstrassSigma L z).analyticOrderAt_eq_zero.2 (weierstrassSigma_ne_zero L hz)

def latticeForm (u v : ℂ) : ℂ := u * conj v / latticeArea L

theorem latticeForm_add_left (u u' v : ℂ) :
    latticeForm L (u + u') v = latticeForm L u v + latticeForm L u' v := by
  simp only [latticeForm]; ring

theorem latticeForm_add_right (u v v' : ℂ) :
    latticeForm L u (v + v') = latticeForm L u v + latticeForm L u v' := by
  simp only [latticeForm, map_add]; ring

theorem latticeForm_mul_left (a u v : ℂ) : latticeForm L (a * u) v = a * latticeForm L u v := by
  simp only [latticeForm]; ring

theorem latticeForm_mul_right (a u v : ℂ) :
    latticeForm L u (a * v) = conj a * latticeForm L u v := by
  simp only [latticeForm, map_mul]; ring

theorem latticeForm_eq_inner (u v : ℂ) : latticeForm L u v = inner ℂ v u / latticeArea L := by
  simp [latticeForm]

theorem conj_latticeForm (u v : ℂ) : conj (latticeForm L u v) = latticeForm L v u := by
  simp [latticeForm, mul_comm]

theorem latticeForm_self (u : ℂ) : latticeForm L u u = (‖u‖ ^ 2 / latticeArea L : ℝ) := by
  simp [latticeForm, mul_conj']

theorem im_latticeForm_int (m n m' n' : ℤ) :
    (latticeForm L (m * L.ω₁ + n * L.ω₂) (m' * L.ω₁ + n' * L.ω₂)).im =
      (n * m' - m * n' : ℤ) * (latticeForm L L.ω₂ L.ω₁).im := by
  simp only [latticeForm, div_ofReal_im]
  simp
  ring

theorem abs_im_latticeForm : |(latticeForm L L.ω₂ L.ω₁).im| = 1 := by
  rw [latticeForm, div_ofReal_im, abs_div, abs_of_pos (latticeArea_pos L), mul_comm,
    ← latticeArea_eq, div_self (latticeArea_pos L).ne']

theorem im_latticeForm_eq_one (h : 0 < (L.ω₂ / L.ω₁).im) : (latticeForm L L.ω₂ L.ω₁).im = 1 := by
  have h1 : L.ω₁ ≠ 0 := by simpa using L.indep.ne_zero 0
  rw [← abs_im_latticeForm L, abs_of_pos]
  rw [latticeForm, div_ofReal_im]
  refine div_pos ?_ (latticeArea_pos L)
  rw [div_im, ← sub_div, div_pos_iff_of_pos_right (normSq_pos.2 h1)] at h
  simp only [mul_im, conj_re, conj_im]
  linarith

theorem exists_int_im_latticeForm {a b : ℂ} (ha : a ∈ L.lattice) (hb : b ∈ L.lattice) :
    ∃ k : ℤ, (latticeForm L a b).im = k := by
  obtain ⟨m, n, rfl⟩ := mem_lattice.1 ha
  obtain ⟨m', n', rfl⟩ := mem_lattice.1 hb
  rw [im_latticeForm_int]
  rcases (abs_eq zero_le_one).1 (abs_im_latticeForm L) with h | h
  · exact ⟨n * m' - m * n', by rw [h, mul_one]⟩
  · exact ⟨-(n * m' - m * n'), by rw [h]; push_cast; ring⟩

theorem IsHomothetic.latticeForm_mul {L L' : PeriodPair} {c : ℂ} (h : IsHomothetic c L L')
    (u v : ℂ) : latticeForm L' (c * u) (c * v) = latticeForm L u v := by
  have hc := h.ne_zero
  have hc' : conj c ≠ 0 := by simpa using hc
  rw [latticeForm, latticeForm, h.latticeArea_eq, map_mul]
  push_cast
  rw [← mul_conj']
  field_simp

theorem quasiPeriod_mul_eq (z w : ℂ) :
    quasiPeriod L w * z = sTwo L * w * z + π * latticeForm L z w := by
  rw [quasiPeriod_eq, latticeForm]; push_cast; ring

def canonicalSigma (z : ℂ) : ℂ := weierstrassSigma L z * cexp (-(sTwo L * z ^ 2 / 2))

@[fun_prop] theorem differentiable_canonicalSigma : Differentiable ℂ (canonicalSigma L) := by
  unfold canonicalSigma; fun_prop

@[simp] theorem canonicalSigma_neg (z : ℂ) : canonicalSigma L (-z) = -canonicalSigma L z := by
  simp [canonicalSigma]

@[simp] theorem canonicalSigma_zero : canonicalSigma L 0 = 0 := by simp [canonicalSigma]

theorem canonicalSigma_eq_zero_iff {z : ℂ} : canonicalSigma L z = 0 ↔ z ∈ L.lattice := by
  rw [canonicalSigma, mul_eq_zero, or_iff_left (exp_ne_zero _), weierstrassSigma_eq_zero_iff]

theorem hasDerivAt_canonicalSigma' (z : ℂ) : HasDerivAt (canonicalSigma L)
    ((deriv (weierstrassSigma L) z - sTwo L * z * weierstrassSigma L z) *
      cexp (-(sTwo L * z ^ 2 / 2))) z :=
  ((differentiable_weierstrassSigma L z).hasDerivAt.fun_mul
    ((((hasDerivAt_pow 2 z).const_mul (sTwo L)).div_const 2).fun_neg.cexp)).congr_deriv
    (by simp; ring)

theorem hasDerivAt_canonicalSigma_zero : HasDerivAt (canonicalSigma L) 1 0 := by
  simpa [(hasDerivAt_weierstrassSigma_zero L).deriv] using hasDerivAt_canonicalSigma' L 0

theorem hasDerivAt_canonicalSigma {z : ℂ} (hz : z ∉ L.lattice) : HasDerivAt (canonicalSigma L)
    ((weierstrassZeta L z - sTwo L * z) * canonicalSigma L z) z :=
  (hasDerivAt_canonicalSigma' L z).congr_deriv (by
    rw [(hasDerivAt_weierstrassSigma L hz).deriv, canonicalSigma]; ring)

theorem analyticOrderAt_canonicalSigma_of_mem {w : ℂ} (hw : w ∈ L.lattice) :
    analyticOrderAt (canonicalSigma L) w = 1 := by
  refine ((differentiable_canonicalSigma L).analyticAt
    w).analyticOrderAt_eq_one_of_zero_deriv_ne_zero ((canonicalSigma_eq_zero_iff L).2 hw) ?_
  rw [(hasDerivAt_canonicalSigma' L w).deriv, (weierstrassSigma_eq_zero_iff L).2 hw, mul_zero,
    sub_zero]
  exact mul_ne_zero (deriv_weierstrassSigma_ne_zero L hw) (exp_ne_zero _)

theorem IsHomothetic.canonicalSigma_mul {L L' : PeriodPair} {c : ℂ} (h : IsHomothetic c L L')
    (z : ℂ) : canonicalSigma L' (c * z) = c * canonicalSigma L z := by
  have := h.ne_zero
  rw [canonicalSigma, h.weierstrassSigma_mul, h.sTwo_eq, canonicalSigma, mul_assoc]
  congr 3
  field_simp

theorem canonicalSigma_add {w : ℂ} (hw : w ∈ L.lattice) (z : ℂ) :
    canonicalSigma L (z + w) = sigmaSign L w *
      cexp (π * latticeForm L z w + π * latticeForm L w w / 2) * canonicalSigma L z := by
  rw [canonicalSigma, canonicalSigma, weierstrassSigma_add L hw]
  have : cexp (quasiPeriod L w * (z + w / 2)) * cexp (-(sTwo L * (z + w) ^ 2 / 2)) =
      cexp (π * latticeForm L z w + π * latticeForm L w w / 2) * cexp (-(sTwo L * z ^ 2 / 2)) := by
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    linear_combination quasiPeriod_mul_eq L z w + quasiPeriod_mul_eq L w w / 2
  linear_combination sigmaSign L w * weierstrassSigma L z * this

theorem sigmaSign_add {a b : ℂ} (ha : a ∈ L.lattice) (hb : b ∈ L.lattice) :
    sigmaSign L (a + b) =
      sigmaSign L a * sigmaSign L b * cexp (π * I * (latticeForm L a b).im) := by
  set x := L.ω₁ / 2
  have hx : canonicalSigma L x ≠ 0 :=
    (canonicalSigma_eq_zero_iff L).not.2 L.ω₁_div_two_notMem_lattice
  have h1 := canonicalSigma_add L (add_mem ha hb) x
  rw [← add_assoc, canonicalSigma_add L hb, canonicalSigma_add L ha] at h1
  have h2 : cexp (π * latticeForm L (x + a) b + π * latticeForm L b b / 2) *
      cexp (π * latticeForm L x a + π * latticeForm L a a / 2) =
      cexp (π * I * (latticeForm L a b).im) *
      cexp (π * latticeForm L x (a + b) + π * latticeForm L (a + b) (a + b) / 2) := by
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    have h3 := sub_conj (latticeForm L a b)
    rw [conj_latticeForm] at h3
    push_cast at h3
    simp only [latticeForm, map_add] at h3 ⊢
    linear_combination (π / 2 : ℂ) * h3
  refine mul_right_cancel₀ (mul_ne_zero (exp_ne_zero
    (π * latticeForm L x (a + b) + π * latticeForm L (a + b) (a + b) / 2)) hx) ?_
  linear_combination sigmaSign L a * sigmaSign L b * canonicalSigma L x * h2 - h1

theorem exists_eq_add_sq_mul_of_even {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (he : ∀ z, f (-z) = f z) :
    ∃ h : ℂ → ℂ, AnalyticAt ℂ h 0 ∧ ∀ z, f z = f 0 + z ^ 2 * h z := by
  obtain ⟨h, hh, e⟩ := hf.exists_eq_sum_add_pow_mul 2
  have h0 : deriv f 0 = 0 := by
    have := deriv_comp_neg f 0
    simp only [he, neg_zero] at this
    exact CharZero.eq_neg_self_iff.1 this
  exact ⟨h, hh, fun z => by simpa [Finset.sum_range_succ, h0] using e z⟩

theorem eq_const_of_periodic_of_tendsto {f : ℂ → ℂ} {c : ℂ}
    (hf : DifferentiableOn ℂ f (L.lattice : Set ℂ)ᶜ)
    (hper : ∀ z ∉ L.lattice, ∀ w ∈ L.lattice, f (z + w) = f z)
    (hc : Tendsto f (𝓝[≠] 0) (𝓝 c)) {z : ℂ} (hz : z ∉ L.lattice) : f z = c := by
  classical
  let g : ℂ → ℂ := fun z => if z ∈ L.lattice then c else f z
  have hg : ∀ z, ∀ w ∈ L.lattice, g (z + w) = g z := by
    intro z w hw
    by_cases hz : z ∈ L.lattice
    · simp only [g, if_pos hz, if_pos (add_mem hz hw)]
    · simp only [g, if_neg hz, if_neg (add_notMem_lattice hz hw), hper z hz w hw]
  have hd : ∀ z ∉ L.lattice, DifferentiableAt ℂ g z := by
    intro z hz
    have hn := L.isClosed_lattice.isOpen_compl.mem_nhds hz
    refine (hf.differentiableAt hn).congr_of_eventuallyEq ?_
    filter_upwards [hn] with x hx using if_neg hx
  have h0 : AnalyticAt ℂ g 0 := by
    refine analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt
      ((eventually_notMem_lattice L 0).mono hd) ?_
    rw [← continuousWithinAt_compl_self, ContinuousWithinAt, show g 0 = c from if_pos (zero_mem _)]
    refine hc.congr' ?_
    filter_upwards [eventually_notMem_lattice L 0] with x hx using (if_neg hx).symm
  have hdiff : Differentiable ℂ g := by
    intro x
    by_cases hx : x ∈ L.lattice
    · have e : g = fun z => g (z + -x) := funext fun z => (hg z _ (neg_mem hx)).symm
      rw [e]
      exact DifferentiableAt.comp (g := g) x (by simpa using h0.differentiableAt) (by fun_prop)
    · exact hd x hx
  have := hdiff.apply_eq_apply_of_bounded
    (IsZLattice.isCompact_range_of_periodic L.lattice _ hdiff.continuous hg).isBounded z 0
  simpa only [g, if_neg hz, if_pos (zero_mem L.lattice)] using this

theorem exists_eq_const_of_periodic_of_even {f N : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (L.lattice : Set ℂ)ᶜ)
    (hper : ∀ z ∉ L.lattice, ∀ w ∈ L.lattice, f (z + w) = f z)
    (hN : AnalyticAt ℂ N 0) (he : ∀ z, N (-z) = N z) (h0 : N 0 = 0)
    (hfN : ∀ z ∉ L.lattice, z ^ 2 * f z = N z) : ∃ c, ∀ z ∉ L.lattice, f z = c := by
  obtain ⟨h, hh, e⟩ := exists_eq_add_sq_mul_of_even hN he
  refine ⟨h 0, fun z hz => eq_const_of_periodic_of_tendsto L hf hper ?_ hz⟩
  refine (hh.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr' ?_
  filter_upwards [eventually_notMem_lattice L 0, self_mem_nhdsWithin] with x hx (hx0 : x ≠ 0)
  have := e x
  rw [h0, zero_add, ← hfN x hx] at this
  exact (mul_left_cancel₀ (pow_ne_zero 2 hx0) this).symm

theorem weierstrassP_sub_weierstrassP {u v : ℂ} (hu : u ∉ L.lattice) (hv : v ∉ L.lattice) :
    ℘[L] u - ℘[L] v = -(weierstrassSigma L (u + v) * weierstrassSigma L (u - v)) /
      (weierstrassSigma L u ^ 2 * weierstrassSigma L v ^ 2) := by
  obtain ⟨c, hc⟩ := exists_eq_const_of_periodic_of_even L
    (f := fun z => weierstrassSigma L (z + v) * weierstrassSigma L (z - v) /
      weierstrassSigma L z ^ 2 + weierstrassSigma L v ^ 2 * ℘[L] z)
    (N := fun z => weierstrassSigma L (z + v) * weierstrassSigma L (z - v) / sigmaProd L z ^ 2 +
      weierstrassSigma L v ^ 2 * (1 + z ^ 2 * weierstrassPExcept L 0 z))
    (.add (.div (by fun_prop) (by fun_prop) fun z hz =>
      pow_ne_zero _ (weierstrassSigma_ne_zero L hz)) (L.differentiableOn_weierstrassP.const_mul _))
    (fun z hz w hw => by
      have hσ := weierstrassSigma_ne_zero L hz
      have hε := sigmaSign_ne_zero L w
      have e : cexp (quasiPeriod L w * (z + v + w / 2)) * cexp (quasiPeriod L w * (z - v + w / 2)) =
          cexp (quasiPeriod L w * (z + w / 2)) ^ 2 := by
        rw [sq, ← Complex.exp_add, ← Complex.exp_add]; congr 1; ring
      beta_reduce
      rw [L.weierstrassP_add_coe z ⟨w, hw⟩, add_right_comm, add_sub_right_comm,
        weierstrassSigma_add L hw, weierstrassSigma_add L hw, weierstrassSigma_add L hw]
      congr 1
      rw [div_eq_div_iff (pow_ne_zero _ (mul_ne_zero (mul_ne_zero hε (exp_ne_zero _)) hσ))
        (pow_ne_zero _ hσ)]
      linear_combination (sigmaSign L w ^ 2 * weierstrassSigma L (z + v) *
        weierstrassSigma L (z - v) * weierstrassSigma L z ^ 2) * e)
    (by
      have h1 := L.analyticAt_weierstrassPExcept 0
      have h2 := (differentiable_sigmaProd L).analyticAt 0
      refine .add (.div (by fun_prop) (by fun_prop) (by simp)) (by fun_prop))
    (fun z => by
      beta_reduce
      rw [show -z + v = -(z - v) by ring, show -z - v = -(z + v) by ring, weierstrassSigma_neg,
        weierstrassSigma_neg, sigmaProd_neg, L.weierstrassPExcept_neg, neg_zero]
      ring)
    (by simp; ring)
    (fun z hz => by
      have h0 : z ≠ 0 := fun h => hz (h ▸ zero_mem _)
      have h1 := sigmaProd_ne_zero L (z := z) fun h => hz h.1
      have h2 := L.weierstrassPExcept_add 0 z
      simp only [ZeroMemClass.coe_zero, sub_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
        zero_pow, div_zero] at h2
      beta_reduce
      rw [← h2, show weierstrassSigma L z = z * sigmaProd L z from rfl]
      field_simp
      ring)
  have h1 := (hc u hu).trans (hc v hv).symm
  have hσu := weierstrassSigma_ne_zero L hu
  have hσv := weierstrassSigma_ne_zero L hv
  simp only [sub_self, weierstrassSigma_zero, mul_zero, zero_div, zero_add] at h1
  field_simp at h1 ⊢
  linear_combination h1

theorem weierstrassP_sub_weierstrassP_canonicalSigma {u v : ℂ} (hu : u ∉ L.lattice)
    (hv : v ∉ L.lattice) :
    ℘[L] u - ℘[L] v = -(canonicalSigma L (u + v) * canonicalSigma L (u - v)) /
      (canonicalSigma L u ^ 2 * canonicalSigma L v ^ 2) := by
  have e : cexp (-(sTwo L * (u + v) ^ 2 / 2)) * cexp (-(sTwo L * (u - v) ^ 2 / 2)) =
      cexp (-(sTwo L * u ^ 2 / 2)) ^ 2 * cexp (-(sTwo L * v ^ 2 / 2)) ^ 2 := by
    simp only [sq (cexp _), ← Complex.exp_add]; congr 1; ring
  have hσu := weierstrassSigma_ne_zero L hu
  have hσv := weierstrassSigma_ne_zero L hv
  rw [weierstrassP_sub_weierstrassP L hu hv, div_eq_div_iff (by positivity) (mul_ne_zero
    (pow_ne_zero _ ((canonicalSigma_eq_zero_iff L).not.2 hu))
    (pow_ne_zero _ ((canonicalSigma_eq_zero_iff L).not.2 hv)))]
  simp only [canonicalSigma]
  linear_combination (weierstrassSigma L (u + v) * weierstrassSigma L (u - v) *
    weierstrassSigma L u ^ 2 * weierstrassSigma L v ^ 2) * e

theorem exists_canonicalSigma_eq : ∃ h : ℂ → ℂ, AnalyticAt ℂ h 0 ∧
    ∀ z, canonicalSigma L z = z + z ^ 3 * h z := by
  obtain ⟨h, hh, e⟩ := exists_eq_add_sq_mul_of_even
    (f := fun z => sigmaProd L z * cexp (-(sTwo L * z ^ 2 / 2)))
    (Differentiable.analyticAt (by fun_prop) 0) (by simp)
  refine ⟨h, hh, fun z => ?_⟩
  rw [canonicalSigma, weierstrassSigma, mul_assoc, e z]
  simp
  ring

theorem canonicalSigma_sub_isBigO :
    (fun z => canonicalSigma L z - z) =O[𝓝 0] fun z : ℂ => z ^ 3 := by
  obtain ⟨h, hh, e⟩ := exists_canonicalSigma_eq L
  simp only [e, add_sub_cancel_left]
  simpa using (Asymptotics.isBigO_refl (fun z : ℂ => z ^ 3) _).mul
    (hh.continuousAt.tendsto.isBigO_one ℂ)

theorem exists_eq_const_of_periodic_of_simple_pole {f N : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (L.lattice : Set ℂ)ᶜ)
    (hper : ∀ z ∉ L.lattice, ∀ w ∈ L.lattice, f (z + w) = f z)
    (hN : AnalyticAt ℂ N 0) (hfN : ∀ᶠ z in 𝓝[≠] 0, z * f z = N z) :
    ∃ c, ∀ z ∉ L.lattice, f z = c := by
  have ho := L.isClosed_lattice.isOpen_compl
  obtain ⟨M, hM, e⟩ := hN.exists_eq_sum_add_pow_mul 1
  simp only [Finset.sum_range_one, pow_zero, Nat.factorial_zero, Nat.cast_one, div_one,
    iteratedDeriv_zero, one_smul, pow_one, smul_eq_mul, one_mul] at e
  set r := N 0
  let h : ℂ → ℂ := fun z => f z - r * weierstrassZeta L z
  have hh : AnalyticOnNhd ℂ h (L.lattice : Set ℂ)ᶜ := fun z hz =>
    (hf.analyticOnNhd ho z hz).sub (analyticAt_const.mul (analyticOnNhd_weierstrassZeta L z hz))
  have hq : ∀ z ∉ L.lattice, ∀ w ∈ L.lattice, h (z + w) = h z - r * quasiPeriod L w := by
    intro z hz w hw
    simp only [h, hper z hz w hw, weierstrassZeta_add L hw hz]
    ring
  have hK : AnalyticAt ℂ (fun z => M z - r * weierstrassZetaExcept L 0 z) 0 :=
    hM.sub (analyticAt_const.mul (analyticAt_weierstrassZetaExcept L 0))
  have hhK : h =ᶠ[𝓝[≠] 0] fun z => M z - r * weierstrassZetaExcept L 0 z := by
    filter_upwards [hfN, self_mem_nhdsWithin] with z hz (hz0 : z ≠ 0)
    rw [e z] at hz
    refine mul_left_cancel₀ hz0 ?_
    simp only [h, weierstrassZeta_eq_inv_add]
    have : z * (1 / z) = 1 := by field_simp
    linear_combination hz - r * this
  obtain ⟨c, hc⟩ : ∃ c, ∀ z ∉ L.lattice, deriv h z = c := by
    refine ⟨_, fun z hz => eq_const_of_periodic_of_tendsto L hh.deriv.differentiableOn
      (fun z hz w hw => ?_) ((hK.deriv.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr'
        hhK.nhdsNE_deriv.symm) hz⟩
    rw [← deriv_comp_add_const]
    refine (EventuallyEq.deriv_eq ?_).trans (deriv_sub_const (r * quasiPeriod L w))
    filter_upwards [ho.mem_nhds hz] with x hx using hq x hx w hw
  have hx := L.ω₁_div_two_notMem_lattice
  set x := L.ω₁ / 2
  have hlin : ∀ z ∉ L.lattice, h z = c * z + (h x - c * x) := fun z hz =>
    eqOn_compl_lattice_of_hasDerivAt L (g := fun z => c * z + (h x - c * x)) (f' := fun _ => c)
      (fun z hz => hc z hz ▸ (hh z hz).differentiableAt.hasDerivAt)
      (fun z _ => by simpa using ((hasDerivAt_id' z).const_mul c).add_const (h x - c * x))
      hx (by ring) hz
  have hcw : ∀ w ∈ L.lattice, c * w = -(r * quasiPeriod L w) := by
    intro w hw
    have h1 := hlin _ (add_notMem_lattice hx hw)
    rw [hq x hx w hw] at h1
    linear_combination -h1
  have hr : r = 0 := by
    have h1 := quasiPeriod_mul_sub L L.ω₁ L.ω₂
    have h2 : (((conj L.ω₁ * L.ω₂).im / latticeArea L : ℝ) : ℂ) ≠ 0 := by
      have hA := latticeArea_pos L
      refine ofReal_ne_zero.2 (div_ne_zero ?_ hA.ne')
      rwa [latticeArea_eq, abs_pos] at hA
    refine mul_right_cancel₀ (mul_ne_zero two_pi_I_ne_zero h2) ?_
    linear_combination L.ω₂ * hcw _ L.ω₁_mem_lattice - L.ω₁ * hcw _ L.ω₂_mem_lattice - r * h1
  have hc0 : c = 0 := by
    have h1 : L.ω₁ ≠ 0 := by simpa using L.indep.ne_zero 0
    simpa [hr, h1] using hcw _ L.ω₁_mem_lattice
  exact ⟨h x, fun z hz => by simpa [h, hr, hc0] using hlin z hz⟩

theorem exists_eq_mul_canonicalSigma {F : ℂ → ℂ} (hF : Differentiable ℂ F)
    (hlaw : ∀ w ∈ L.lattice, ∀ z, F (z + w) =
      sigmaSign L w * cexp (π * latticeForm L z w + π * latticeForm L w w / 2) * F z) :
    ∃ c : ℂ, ∀ z, F z = c * canonicalSigma L z := by
  have hne : ∀ z ∉ L.lattice, canonicalSigma L z ≠ 0 := fun z hz =>
    (canonicalSigma_eq_zero_iff L).not.2 hz
  obtain ⟨c, hc⟩ := exists_eq_const_of_periodic_of_simple_pole L
    (f := fun z => F z / canonicalSigma L z)
    (N := fun z => F z / (sigmaProd L z * cexp (-(sTwo L * z ^ 2 / 2))))
    (.div hF.differentiableOn (differentiable_canonicalSigma L).differentiableOn hne)
    (fun z hz w hw => by
      beta_reduce
      rw [hlaw w hw, canonicalSigma_add L hw,
        mul_div_mul_left _ _ (mul_ne_zero (sigmaSign_ne_zero L w) (exp_ne_zero _))])
    ((hF.analyticAt 0).div (Differentiable.analyticAt (by fun_prop) 0) (by simp))
    (by
      filter_upwards [self_mem_nhdsWithin] with z (hz : z ≠ 0)
      rw [canonicalSigma, weierstrassSigma, mul_assoc, ← mul_div_assoc, mul_div_mul_left _ _ hz])
  refine ⟨c, fun z => congrFun (Continuous.ext_on (dense_compl_lattice L) hF.continuous
    (g := fun z => c * canonicalSigma L z)
    (continuous_const.mul (differentiable_canonicalSigma L).continuous) fun z hz => ?_) z⟩
  exact (div_eq_iff (hne z hz)).1 (hc z hz)

def periodsOfUpperHalfPlane (τ : UpperHalfPlane) : PeriodPair where
  ω₁ := 1
  ω₂ := τ
  indep := by
    rw [LinearIndependent.pair_iff]
    intro s t h
    have h1 := congrArg Complex.im h
    have h2 := congrArg Complex.re h
    simp [τ.im_ne_zero] at h1
    simp [h1] at h2
    exact ⟨h2, h1⟩

theorem latticeArea_periodsOfUpperHalfPlane (τ : UpperHalfPlane) :
    latticeArea (periodsOfUpperHalfPlane τ) = τ.im := by
  simp [latticeArea_eq, periodsOfUpperHalfPlane, abs_of_pos τ.im_pos]

theorem isHomothetic_I_gaussian : IsHomothetic I (periodsOfUpperHalfPlane UpperHalfPlane.I)
    (periodsOfUpperHalfPlane UpperHalfPlane.I) := by
  intro x
  simp only [mem_lattice, periodsOfUpperHalfPlane, UpperHalfPlane.coe_I]
  constructor
  · rintro ⟨m, n, h⟩
    exact ⟨n, -m, by push_cast; linear_combination -I * h + (n - x) * I_mul_I⟩
  · rintro ⟨m, n, h⟩
    exact ⟨-n, m, by push_cast; linear_combination I * h - n * I_mul_I⟩

theorem sTwo_gaussian : sTwo (periodsOfUpperHalfPlane UpperHalfPlane.I) = 0 := by
  have := isHomothetic_I_gaussian.sTwo_eq
  rw [I_sq] at this
  linear_combination this / 2

example : quasiPeriod (periodsOfUpperHalfPlane UpperHalfPlane.I) 1 = π ∧
    quasiPeriod (periodsOfUpperHalfPlane UpperHalfPlane.I) I = -(π * I) ∧
    weierstrassZeta (periodsOfUpperHalfPlane UpperHalfPlane.I) (1 / 2) = π / 2 := by
  have h : quasiPeriod (periodsOfUpperHalfPlane UpperHalfPlane.I) 1 = π := by
    simp [quasiPeriod_eq, sTwo_gaussian, latticeArea_periodsOfUpperHalfPlane]
  refine ⟨h, ?_, ?_⟩
  · simp [quasiPeriod_eq, sTwo_gaussian, latticeArea_periodsOfUpperHalfPlane]
  · have h1 := quasiPeriod_ω₁ (periodsOfUpperHalfPlane UpperHalfPlane.I)
    change quasiPeriod _ 1 = 2 * weierstrassZeta _ (1 / 2) at h1
    linear_combination (h - h1) / 2

example (z : ℂ) : weierstrassSigma (periodsOfUpperHalfPlane UpperHalfPlane.I) (z + 1) =
    -cexp (π * (z + 1 / 2)) * weierstrassSigma (periodsOfUpperHalfPlane UpperHalfPlane.I) z := by
  rw [weierstrassSigma_add _ (w := 1) (ω₁_mem_lattice _),
    sigmaSign_of_notMem _ (w := 1) (ω₁_div_two_notMem_lattice _)]
  simp [quasiPeriod_eq, sTwo_gaussian, latticeArea_periodsOfUpperHalfPlane]

example : sigmaSign L L.ω₁ = -1 ∧ sigmaSign L L.ω₂ = -1 ∧ sigmaSign L (L.ω₁ + L.ω₂) = -1 ∧
    sigmaSign L (2 * L.ω₁) = 1 :=
  ⟨by simpa using sigmaSign_int L 1 0, by simpa using sigmaSign_int L 0 1,
    by simpa [show (-1 : ℂ) ^ (3 : ℤ) = -1 by norm_num] using sigmaSign_int L 1 1,
    by simpa using sigmaSign_int L 2 0⟩

end GlobalTheory
