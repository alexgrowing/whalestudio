import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.CmLatticeCommutatorPairingPowEqOneOfGoodLift
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.WeierstrassPAddOfNeOfDerivNeZero

open PowerSeries GlobalTheory.MomOne Filter PeriodPair
open scoped ComplexConjugate BigOperators Topology

namespace GlobalTheory.MomOne.UW

variable {q : ℕ} [Fact q.Prime] (M : Mdl q)

lemma g₂_eq (h : M.Ok) : M.L.g₂ = M.c ^ 4 * (((M.ι.symm M.W.a₁ ^ 2 + 4 * M.ι.symm M.W.a₂) ^ 2 -
    24 * (2 * M.ι.symm M.W.a₄ + M.ι.symm M.W.a₁ * M.ι.symm M.W.a₃)) / 12) := by
  obtain ⟨hc, -, -, -, -, -, -, h4, -⟩ := h
  have hc4 := congrArg M.ι.symm h4
  simp only [RingEquiv.symm_apply_apply, map_div₀, WeierstrassCurve.c₄, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, map_sub, map_add, map_mul, map_pow, map_ofNat] at hc4
  have hc0 : M.c ^ 4 ≠ 0 := pow_ne_zero 4 hc
  field_simp at hc4 ⊢
  linear_combination -hc4

lemma g₃_eq (h : M.Ok) : M.L.g₃ = M.c ^ 6 * ((-(M.ι.symm M.W.a₁ ^ 2 + 4 * M.ι.symm M.W.a₂) ^ 3 +
    36 * (M.ι.symm M.W.a₁ ^ 2 + 4 * M.ι.symm M.W.a₂) *
      (2 * M.ι.symm M.W.a₄ + M.ι.symm M.W.a₁ * M.ι.symm M.W.a₃) -
    216 * (M.ι.symm M.W.a₃ ^ 2 + 4 * M.ι.symm M.W.a₆)) / 216) := by
  obtain ⟨hc, -, -, -, -, -, -, -, h6⟩ := h
  have hc6 := congrArg M.ι.symm h6
  simp only [RingEquiv.symm_apply_apply, map_div₀, WeierstrassCurve.c₆, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, map_sub, map_add, map_mul, map_pow, map_ofNat, map_neg] at hc6
  have hc0 : M.c ^ 6 ≠ 0 := pow_ne_zero 6 hc
  field_simp at hc6 ⊢
  linear_combination -hc6

lemma x_eq (z : ℂ) : M.x z =
    ℘[M.L] z / M.c ^ 2 - (M.ι.symm M.W.a₁ ^ 2 + 4 * M.ι.symm M.W.a₂) / 12 := by
  simp only [Mdl.x, WeierstrassCurve.b₂, map_div₀, map_add, map_mul, map_pow, map_ofNat]

lemma charpoly_eq_of_isIso (h : M.Ok) (z : ℂ) : ℘[M.L] z =
    M.c ^ 2 * (M.x z + (M.ι.symm M.W.a₁ ^ 2 + 4 * M.ι.symm M.W.a₂) / 12) := by
  have hc : M.c ≠ 0 := h.1
  rw [x_eq M z]
  field_simp
  ring

lemma P'_eq (h : M.Ok) (z : ℂ) : ℘'[M.L] z =
    M.c ^ 3 * (2 * M.y z + M.ι.symm M.W.a₁ * M.x z + M.ι.symm M.W.a₃) := by
  have hc : M.c ≠ 0 := h.1
  simp only [Mdl.y]
  field_simp
  ring

lemma equation (h : M.Ok) {z : ℂ} (hz : z ∉ M.L.lattice) :
    M.y z ^ 2 + M.ι.symm M.W.a₁ * M.x z * M.y z + M.ι.symm M.W.a₃ * M.y z =
      M.x z ^ 3 + M.ι.symm M.W.a₂ * M.x z ^ 2 + M.ι.symm M.W.a₄ * M.x z + M.ι.symm M.W.a₆ := by
  have hc : M.c ≠ 0 := h.1
  have key := M.L.derivWeierstrassP_sq z hz
  rw [P'_eq M h z, charpoly_eq_of_isIso M h z, g₂_eq M h, g₃_eq M h] at key
  have h4 : (4 * M.c ^ 6) * ((M.y z ^ 2 + M.ι.symm M.W.a₁ * M.x z * M.y z + M.ι.symm M.W.a₃ * M.y z) -
      (M.x z ^ 3 + M.ι.symm M.W.a₂ * M.x z ^ 2 + M.ι.symm M.W.a₄ * M.x z + M.ι.symm M.W.a₆)) = 0 := by
    linear_combination key
  have h46 : (4 * M.c ^ 6) ≠ 0 := mul_ne_zero (by norm_num) (pow_ne_zero 6 hc)
  exact sub_eq_zero.mp ((mul_eq_zero.mp h4).resolve_left h46)

lemma hasDerivAt_x_of_not_mem_lattice (h : M.Ok) {z : ℂ} (hz : z ∉ M.L.lattice) :
    HasDerivAt M.x (M.c * (2 * M.y z + M.ι.symm M.W.a₁ * M.x z + M.ι.symm M.W.a₃)) z := by
  have hc : M.c ≠ 0 := h.1
  have hd := ((GlobalTheory.hasDerivAt_weierstrassP M.L hz).div_const (M.c ^ 2)).sub_const (M.ι.symm (M.W.b₂ / 12))
  refine hd.congr_deriv ?_
  rw [P'_eq M h z]
  field_simp

lemma hasDerivAt_y (h : M.Ok) {z : ℂ} (hz : z ∉ M.L.lattice) :
    HasDerivAt M.y (M.c * (3 * M.x z ^ 2 + 2 * M.ι.symm M.W.a₂ * M.x z + M.ι.symm M.W.a₄ -
      M.ι.symm M.W.a₁ * M.y z)) z := by
  have hc : M.c ≠ 0 := h.1
  have hx := hasDerivAt_x_of_not_mem_lattice M h hz
  have hd := ((((GlobalTheory.hasDerivAt_derivWeierstrassP M.L hz).div_const (M.c ^ 3)).sub
    (hx.const_mul (M.ι.symm M.W.a₁))).sub_const (M.ι.symm M.W.a₃)).div_const 2
  refine hd.congr_deriv ?_
  rw [charpoly_eq_of_isIso M h z, g₂_eq M h]
  field_simp
  ring

lemma analyticAt_x_of_not_mem_lattice {z : ℂ} (hz : z ∉ M.L.lattice) : AnalyticAt ℂ M.x z := by
  have := M.L.analyticOnNhd_weierstrassP z hz
  show AnalyticAt ℂ (fun t => ℘[M.L] t / M.c ^ 2 - M.ι.symm (M.W.b₂ / 12)) z
  fun_prop

lemma analyticAt_y {z : ℂ} (hz : z ∉ M.L.lattice) : AnalyticAt ℂ M.y z := by
  have h1 := M.L.analyticOnNhd_derivWeierstrassP z hz
  have h2 := analyticAt_x_of_not_mem_lattice M hz
  show AnalyticAt ℂ (fun t => (℘'[M.L] t / M.c ^ 3 - M.ι.symm M.W.a₁ * M.x t - M.ι.symm M.W.a₃) / 2) z
  fun_prop

lemma meromorphic_x : Meromorphic M.x := by
  show Meromorphic (fun t => ℘[M.L] t / M.c ^ 2 - M.ι.symm (M.W.b₂ / 12))
  fun_prop

lemma meromorphic_y : Meromorphic M.y := by
  have := meromorphic_x M
  show Meromorphic (fun t => (℘'[M.L] t / M.c ^ 3 - M.ι.symm M.W.a₁ * M.x t - M.ι.symm M.W.a₃) / 2)
  fun_prop

lemma x_add {l : ℂ} (hl : l ∈ M.L.lattice) (z : ℂ) : M.x (z + l) = M.x z := by
  have hp := M.L.weierstrassP_add_coe z ⟨l, hl⟩
  simp only at hp
  simp only [Mdl.x, hp]

lemma y_add {l : ℂ} (hl : l ∈ M.L.lattice) (z : ℂ) : M.y (z + l) = M.y z := by
  have hp := M.L.derivWeierstrassP_add_coe z ⟨l, hl⟩
  simp only at hp
  simp only [Mdl.y, hp, x_add M hl]

lemma ell_u : Ell M.L M.u := by
  refine ⟨fun z₀ => ?_, fun l hl z => ?_⟩
  · have hm : MeromorphicAt (fun t => -M.x t / M.y t) z₀ := by
      have := meromorphic_x M z₀
      have := meromorphic_y M z₀
      fun_prop
    refine hm.congr ?_
    filter_upwards [GlobalTheory.eventually_ne_notMem_periodLattice M.L z₀] with t ht
    simp [Mdl.u, ht]
  · have hmem : z + l ∈ M.L.lattice ↔ z ∈ M.L.lattice := add_mem_cancel_right hl
    by_cases hz : z ∈ M.L.lattice
    · have hz' := hmem.mpr hz
      simp [Mdl.u, hz, hz']
    · have hz' : z + l ∉ M.L.lattice := fun h' => hz (hmem.mp h')
      simp [Mdl.u, hz, hz', x_add M hl, y_add M hl]

lemma ell_w : Ell M.L M.w := by
  refine ⟨fun z₀ => ?_, fun l hl z => ?_⟩
  · have hm : MeromorphicAt (fun t => -1 / M.y t) z₀ := by
      have := meromorphic_y M z₀
      fun_prop
    refine hm.congr ?_
    filter_upwards [GlobalTheory.eventually_ne_notMem_periodLattice M.L z₀] with t ht
    simp [Mdl.w, ht]
  · have hmem : z + l ∈ M.L.lattice ↔ z ∈ M.L.lattice := add_mem_cancel_right hl
    by_cases hz : z ∈ M.L.lattice
    · have hz' := hmem.mpr hz
      simp [Mdl.w, hz, hz']
    · have hz' : z + l ∉ M.L.lattice := fun h' => hz (hmem.mp h')
      simp [Mdl.w, hz, hz', y_add M hl]

lemma u_ev {z : ℂ} (hz : z ∉ M.L.lattice) : M.u =ᶠ[𝓝 z] fun t => -M.x t / M.y t := by
  filter_upwards [GlobalTheory.eventually_notMem_periodLattice M.L hz] with t ht
  simp [Mdl.u, ht]

lemma w_ev {z : ℂ} (hz : z ∉ M.L.lattice) : M.w =ᶠ[𝓝 z] fun t => -1 / M.y t := by
  filter_upwards [GlobalTheory.eventually_notMem_periodLattice M.L hz] with t ht
  simp [Mdl.w, ht]

lemma analyticAt_uw {z : ℂ} (hz : z ∉ M.L.lattice) (hy : M.y z ≠ 0) :
    AnalyticAt ℂ M.u z ∧ AnalyticAt ℂ M.w z := by
  have hx := analyticAt_x_of_not_mem_lattice M hz
  have hy' := analyticAt_y M hz
  refine ⟨?_, ?_⟩
  · exact (hx.neg.div hy' hy).congr (u_ev M hz).symm
  · exact ((analyticAt_const (v := (-1 : ℂ))).div hy' hy).congr (w_ev M hz).symm

lemma flow_off (h : M.Ok) {z : ℂ} (hz : z ∉ M.L.lattice) (hy : M.y z ≠ 0) :
    M.w z = M.u z ^ 3 + M.ι.symm M.W.a₁ * M.u z * M.w z + M.ι.symm M.W.a₂ * M.u z ^ 2 * M.w z +
      M.ι.symm M.W.a₃ * M.w z ^ 2 + M.ι.symm M.W.a₄ * M.u z * M.w z ^ 2 +
      M.ι.symm M.W.a₆ * M.w z ^ 3 ∧
    deriv M.u z = M.c * (1 - M.ι.symm M.W.a₁ * M.u z - M.ι.symm M.W.a₂ * M.u z ^ 2 -
      2 * M.ι.symm M.W.a₃ * M.w z - 2 * M.ι.symm M.W.a₄ * M.u z * M.w z -
      3 * M.ι.symm M.W.a₆ * M.w z ^ 2) ∧
    deriv M.w z = M.c * (3 * M.u z ^ 2 + M.ι.symm M.W.a₁ * M.w z +
      2 * M.ι.symm M.W.a₂ * M.u z * M.w z + M.ι.symm M.W.a₄ * M.w z ^ 2) := by
  have hc : M.c ≠ 0 := h.1
  have heq := equation M h hz
  have hinv : M.y z * (M.y z)⁻¹ = 1 := mul_inv_cancel₀ hy
  have hu : M.u z = -M.x z / M.y z := by simp [Mdl.u, hz]
  have hw : M.w z = -1 / M.y z := by simp [Mdl.w, hz]
  have hx := hasDerivAt_x_of_not_mem_lattice M h hz
  have hyd := hasDerivAt_y M h hz
  have hdu : HasDerivAt (fun t => -M.x t / M.y t)
      ((-(M.c * (2 * M.y z + M.ι.symm M.W.a₁ * M.x z + M.ι.symm M.W.a₃)) * M.y z - (-M.x z) * (M.c * (3 * M.x z ^ 2 + 2 * M.ι.symm M.W.a₂ * M.x z + M.ι.symm M.W.a₄ - M.ι.symm M.W.a₁ * M.y z))) / M.y z ^ 2) z := hx.neg.div hyd hy
  have hdw : HasDerivAt (fun t => -1 / M.y t) ((0 * M.y z - (-1) * (M.c * (3 * M.x z ^ 2 + 2 * M.ι.symm M.W.a₂ * M.x z + M.ι.symm M.W.a₄ - M.ι.symm M.W.a₁ * M.y z))) / M.y z ^ 2) z :=
    (hasDerivAt_const z (-1 : ℂ)).div hyd hy
  refine ⟨?_, ?_, ?_⟩
  · rw [hu, hw]
    linear_combination (-(M.y z)⁻¹ ^ 3) * heq +
      ((M.y z)⁻¹ * (M.y z * (M.y z)⁻¹ + 1) + M.ι.symm M.W.a₁ * M.x z * (M.y z)⁻¹ ^ 2 +
        M.ι.symm M.W.a₃ * (M.y z)⁻¹ ^ 2) * hinv
  · rw [(u_ev M hz).deriv_eq, hdu.deriv, hu, hw]
    linear_combination (-3 * M.c * (M.y z)⁻¹ ^ 2) * heq +
      (M.c * (M.y z * (M.y z)⁻¹ + 1) + M.c * M.ι.symm M.W.a₁ * M.x z * (M.y z)⁻¹ +
        2 * M.c * M.ι.symm M.W.a₃ * (M.y z)⁻¹) * hinv
  · rw [(w_ev M hz).deriv_eq, hdw.deriv, hu, hw]
    linear_combination (-M.c * M.ι.symm M.W.a₁ * (M.y z)⁻¹) * hinv

private lemma exists_analytic_u_w_factor_near_lattice (h : M.Ok) {l : ℂ} (hl : l ∈ M.L.lattice) :
    ∃ f g : ℂ → ℂ, AnalyticAt ℂ f l ∧ AnalyticAt ℂ g l ∧ f l = M.c ∧ g l = 0 ∧
      ∀ᶠ z in 𝓝 l, M.u z = (z - l) * f z ∧ M.w z = (z - l) * g z ∧
        (z ≠ l → z ∉ M.L.lattice ∧ M.y z ≠ 0) := by
  have hc : M.c ≠ 0 := h.1
  obtain ⟨Xt, hXdef⟩ : ∃ Xt : ℂ → ℂ, Xt = fun z => ((z - l) ^ 2 * (℘[M.L - l] z - 1 / l ^ 2) + 1) / M.c ^ 2 -
      M.ι.symm (M.W.b₂ / 12) * (z - l) ^ 2 := ⟨_, rfl⟩
  obtain ⟨Yt, hYdef⟩ : ∃ Yt : ℂ → ℂ, Yt = fun z => (((z - l) ^ 3 * ℘'[M.L - l] z - 2) / M.c ^ 3 -
      M.ι.symm M.W.a₁ * (z - l) * Xt z - M.ι.symm M.W.a₃ * (z - l) ^ 3) / 2 := ⟨_, rfl⟩
  have hP0 := M.L.analyticAt_weierstrassPExcept l
  have hD0 := M.L.analyticAt_derivWeierstrassPExcept l
  have hXt : AnalyticAt ℂ Xt l := by
    rw [hXdef]
    fun_prop
  have hYt : AnalyticAt ℂ Yt l := by
    rw [hYdef]
    fun_prop
  have hXl : Xt l = 1 / M.c ^ 2 := by
    rw [hXdef]
    beta_reduce
    ring
  have hYl : Yt l = -1 / M.c ^ 3 := by
    rw [hYdef]
    beta_reduce
    ring
  have hYne : Yt l ≠ 0 := by
    rw [hYl]
    exact div_ne_zero (by norm_num) (pow_ne_zero 3 hc)
  have hf : AnalyticAt ℂ (fun z => -Xt z / Yt z) l := hXt.neg.div hYt hYne
  have hg : AnalyticAt ℂ (fun z => -(z - l) ^ 2 / Yt z) l := by
    have hs : AnalyticAt ℂ (fun z => -(z - l) ^ 2) l := by fun_prop
    exact hs.div hYt hYne
  have hfl : -Xt l / Yt l = M.c := by
    rw [hXl, hYl]
    field_simp
  have hev1 : ∀ᶠ z in 𝓝 l, Yt z ≠ 0 := hYt.continuousAt.eventually_ne hYne
  have hev2 : ∀ᶠ z in 𝓝 l, z ≠ l → z ∉ M.L.lattice :=
    eventually_nhdsWithin_iff.mp (GlobalTheory.eventually_ne_notMem_periodLattice M.L l)
  refine ⟨fun z => -Xt z / Yt z, fun z => -(z - l) ^ 2 / Yt z, hf, hg, hfl, by simp, ?_⟩
  filter_upwards [hev1, hev2] with z hz1 hz2
  by_cases hzl : z = l
  · rw [hzl]
    exact ⟨by simp [Mdl.u, hl], by simp [Mdl.w, hl], fun h' => absurd rfl h'⟩
  have hzL := hz2 hzl
  have hs : z - l ≠ 0 := sub_ne_zero.mpr hzl
  have hP : ℘[M.L] z = ℘[M.L - l] z - 1 / l ^ 2 + 1 / (z - l) ^ 2 := by
    have e := M.L.weierstrassPExcept_def ⟨l, hl⟩ z
    linear_combination -e
  have hD : ℘'[M.L] z = ℘'[M.L - l] z - 2 / (z - l) ^ 3 := by
    have e := M.L.derivWeierstrassPExcept_def ⟨l, hl⟩ z
    linear_combination -e
  have hx : (z - l) ^ 2 * M.x z = Xt z := by
    rw [hXdef]
    simp only [Mdl.x, hP]
    field_simp
  have hy : (z - l) ^ 3 * M.y z = Yt z := by
    rw [hYdef]
    simp only [Mdl.y, hD]
    rw [← hx]
    field_simp
  have hy0 : M.y z ≠ 0 := by
    intro h0
    apply hz1
    rw [← hy, h0, mul_zero]
  refine ⟨?_, ?_, fun _ => ⟨hzL, hy0⟩⟩
  · simp only [Mdl.u, if_neg hzL]
    rw [← hx, ← hy]
    field_simp
  · simp only [Mdl.w, if_neg hzL]
    rw [← hy]
    field_simp

lemma norm_x_lt (h : M.Ok) {z : ℂ} (hz : z ∉ M.L.lattice) (hx : 1 < ‖M.ι (M.x z)‖) :
    ‖M.ι (M.x z)‖ < ‖M.ι (M.y z)‖ := by
  have heq := congrArg M.ι (equation M h hz)
  simp only [map_add, map_mul, map_pow, RingEquiv.apply_symm_apply] at heq
  obtain ⟨-, h1, h2, h3, h4, h6, -, -, -⟩ := h
  by_contra hY'
  have hY := not_lt.mp hY'
  have hmax : ∀ (a b : ℂ_[q]) (B : ℝ), ‖a‖ ≤ B → ‖b‖ ≤ B → ‖a + b‖ ≤ B := fun a b B ha hb =>
    (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb)
  have hX0 : 0 ≤ ‖M.ι (M.x z)‖ := norm_nonneg _
  have hX2 : ‖M.ι (M.x z)‖ ≤ ‖M.ι (M.x z)‖ ^ 2 := by nlinarith
  have hX1 : (1 : ℝ) ≤ ‖M.ι (M.x z)‖ ^ 2 := by nlinarith
  have hL : ‖M.ι (M.y z) ^ 2 + M.W.a₁ * M.ι (M.x z) * M.ι (M.y z) + M.W.a₃ * M.ι (M.y z)‖ ≤
      ‖M.ι (M.x z)‖ ^ 2 := by
    refine hmax _ _ _ (hmax _ _ _ ?_ ?_) ?_
    · rw [norm_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) hY 2
    · rw [norm_mul, norm_mul]
      calc ‖M.W.a₁‖ * ‖M.ι (M.x z)‖ * ‖M.ι (M.y z)‖ ≤ 1 * ‖M.ι (M.x z)‖ * ‖M.ι (M.x z)‖ := by gcongr
        _ = ‖M.ι (M.x z)‖ ^ 2 := by ring
    · rw [norm_mul]
      calc ‖M.W.a₃‖ * ‖M.ι (M.y z)‖ ≤ 1 * ‖M.ι (M.x z)‖ := by gcongr
        _ ≤ ‖M.ι (M.x z)‖ ^ 2 := by linarith
  have hR : ‖M.W.a₂ * M.ι (M.x z) ^ 2 + M.W.a₄ * M.ι (M.x z) + M.W.a₆‖ ≤ ‖M.ι (M.x z)‖ ^ 2 := by
    refine hmax _ _ _ (hmax _ _ _ ?_ ?_) ?_
    · rw [norm_mul, norm_pow]
      calc ‖M.W.a₂‖ * ‖M.ι (M.x z)‖ ^ 2 ≤ 1 * ‖M.ι (M.x z)‖ ^ 2 := by gcongr
        _ = ‖M.ι (M.x z)‖ ^ 2 := by ring
    · rw [norm_mul]
      calc ‖M.W.a₄‖ * ‖M.ι (M.x z)‖ ≤ 1 * ‖M.ι (M.x z)‖ := by gcongr
        _ ≤ ‖M.ι (M.x z)‖ ^ 2 := by linarith
    · linarith
  have hX3 : M.ι (M.x z) ^ 3 = (M.ι (M.y z) ^ 2 + M.W.a₁ * M.ι (M.x z) * M.ι (M.y z) + M.W.a₃ * M.ι (M.y z)) +
      -(M.W.a₂ * M.ι (M.x z) ^ 2 + M.W.a₄ * M.ι (M.x z) + M.W.a₆) := by
    rw [heq]
    ring
  have hcube : ‖M.ι (M.x z)‖ ^ 3 ≤ ‖M.ι (M.x z)‖ ^ 2 := by
    rw [← norm_pow, hX3]
    exact hmax _ _ _ hL (by rw [norm_neg]; exact hR)
  nlinarith

end GlobalTheory.MomOne.UW

namespace GlobalTheory.MomOne
open UW

theorem uw_elliptic_flow : ∀ (q : ℕ) [Fact q.Prime] (M : Mdl q), M.Ok → Ell M.L M.u ∧ Ell M.L M.w ∧ Ell M.L M.x ∧ Ell M.L M.y ∧ M.u 0 = 0 ∧ M.w 0 = 0 ∧ deriv M.u 0 = M.c ∧ (∀ z, z ∉ M.L.lattice → AnalyticAt ℂ M.x z ∧ AnalyticAt ℂ M.y z) ∧ ∀ z₀, M.Small z₀ → AnalyticAt ℂ M.u z₀ ∧ AnalyticAt ℂ M.w z₀ ∧ ‖M.ι (M.u z₀)‖ < 1 ∧ ‖M.ι (M.w z₀)‖ < 1 ∧ (∀ᶠ z in 𝓝[≠] z₀, z ∉ M.L.lattice ∧ M.y z ≠ 0 ∧ M.x z * M.w z = M.u z ∧ M.y z * M.w z = -1) ∧ ∀ᶠ z in 𝓝 z₀, (let a₁ := M.ι.symm M.W.a₁; let a₂ := M.ι.symm M.W.a₂; let a₃ := M.ι.symm M.W.a₃; let a₄ := M.ι.symm M.W.a₄; let a₆ := M.ι.symm M.W.a₆; let u := M.u z; let w := M.w z; w = u ^ 3 + a₁ * u * w + a₂ * u ^ 2 * w + a₃ * w ^ 2 + a₄ * u * w ^ 2 + a₆ * w ^ 3 ∧ deriv M.u z = M.c * (1 - a₁ * u - a₂ * u ^ 2 - 2 * a₃ * w - 2 * a₄ * u * w - 3 * a₆ * w ^ 2) ∧ deriv M.w z = M.c * (3 * u ^ 2 + a₁ * w + 2 * a₂ * u * w + a₄ * w ^ 2)) := by
  intro q _ M h
  have h0 : (0 : ℂ) ∈ M.L.lattice := zero_mem _
  have hlat : ∀ l ∈ M.L.lattice, AnalyticAt ℂ M.u l ∧ AnalyticAt ℂ M.w l ∧ deriv M.u l = M.c ∧
      deriv M.w l = 0 ∧ ∀ᶠ z in 𝓝 l, z ≠ l → z ∉ M.L.lattice ∧ M.y z ≠ 0 := by
    intro l hl
    obtain ⟨f, g, hf, hg, hfl, hgl, hev⟩ := UW.exists_analytic_u_w_factor_near_lattice M h hl
    have hu : M.u =ᶠ[𝓝 l] fun z => (z - l) * f z := hev.mono fun z hz => hz.1
    have hw : M.w =ᶠ[𝓝 l] fun z => (z - l) * g z := hev.mono fun z hz => hz.2.1
    have hdu : HasDerivAt (fun z => (z - l) * f z) (1 * f l + (l - l) * deriv f l) l :=
      ((hasDerivAt_id' l).sub_const l).mul hf.differentiableAt.hasDerivAt
    have hdw : HasDerivAt (fun z => (z - l) * g z) (1 * g l + (l - l) * deriv g l) l :=
      ((hasDerivAt_id' l).sub_const l).mul hg.differentiableAt.hasDerivAt
    have hfa : AnalyticAt ℂ (fun z => (z - l) * f z) l := by fun_prop
    have hga : AnalyticAt ℂ (fun z => (z - l) * g z) l := by fun_prop
    refine ⟨hfa.congr hu.symm, hga.congr hw.symm, ?_, ?_, hev.mono fun z hz => hz.2.2⟩
    · rw [hu.deriv_eq, hdu.deriv]
      simp [hfl]
    · rw [hw.deriv_eq, hdw.deriv]
      simp [hgl]
  refine ⟨UW.ell_u M, UW.ell_w M, ⟨UW.meromorphic_x M, fun l hl z => UW.x_add M hl z⟩,
    ⟨UW.meromorphic_y M, fun l hl z => UW.y_add M hl z⟩, by simp [Mdl.u, h0], by simp [Mdl.w, h0],
    (hlat 0 h0).2.2.1, fun z hz => ⟨UW.analyticAt_x_of_not_mem_lattice M hz, UW.analyticAt_y M hz⟩, ?_⟩
  intro z₀ hs
  by_cases hl : z₀ ∈ M.L.lattice
  · obtain ⟨hua, hwa, hdu, hdw, hev⟩ := hlat z₀ hl
    have hu0 : M.u z₀ = 0 := by simp [Mdl.u, hl]
    have hw0 : M.w z₀ = 0 := by simp [Mdl.w, hl]
    refine ⟨hua, hwa, by simp [hu0], by simp [hw0], ?_, ?_⟩
    · rw [eventually_nhdsWithin_iff]
      filter_upwards [hev] with z hz hne
      obtain ⟨hzL, hy⟩ := hz hne
      have hu : M.u z = -M.x z / M.y z := by simp [Mdl.u, hzL]
      have hw : M.w z = -1 / M.y z := by simp [Mdl.w, hzL]
      refine ⟨hzL, hy, ?_, ?_⟩
      · rw [hu, hw]
        ring
      · rw [hw]
        field_simp
    · filter_upwards [hev] with z hz
      by_cases hne : z = z₀
      · rw [hne]
        simp [hu0, hw0, hdu, hdw]
      · obtain ⟨hzL, hy⟩ := hz hne
        exact UW.flow_off M h hzL hy
  · have hx1 : 1 < ‖M.ι (M.x z₀)‖ := hs.resolve_left hl
    have hlt := UW.norm_x_lt M h hl hx1
    have hYpos : 0 < ‖M.ι (M.y z₀)‖ := lt_trans (lt_trans zero_lt_one hx1) hlt
    have hy : M.y z₀ ≠ 0 := fun h0 => by simp [h0] at hYpos
    obtain ⟨hua, hwa⟩ := UW.analyticAt_uw M hl hy
    have hu0 : M.u z₀ = -M.x z₀ / M.y z₀ := by simp [Mdl.u, hl]
    have hw0 : M.w z₀ = -1 / M.y z₀ := by simp [Mdl.w, hl]
    have hev1 := GlobalTheory.eventually_notMem_periodLattice M.L hl
    have hev2 := (UW.analyticAt_y M hl).continuousAt.eventually_ne hy
    refine ⟨hua, hwa, ?_, ?_, ?_, ?_⟩
    · rw [hu0, map_div₀, map_neg, norm_div, norm_neg, div_lt_one hYpos]
      exact hlt
    · rw [hw0, map_div₀, map_neg, map_one, norm_div, norm_neg, norm_one, div_lt_one hYpos]
      exact lt_trans hx1 hlt
    · filter_upwards [nhdsWithin_le_nhds hev1, nhdsWithin_le_nhds hev2] with z hzL hyz
      have hu : M.u z = -M.x z / M.y z := by simp [Mdl.u, hzL]
      have hw : M.w z = -1 / M.y z := by simp [Mdl.w, hzL]
      refine ⟨hzL, hyz, ?_, ?_⟩
      · rw [hu, hw]
        ring
      · rw [hw]
        field_simp
    · filter_upwards [hev1, hev2] with z hzL hyz
      exact UW.flow_off M h hzL hyz

end GlobalTheory.MomOne
