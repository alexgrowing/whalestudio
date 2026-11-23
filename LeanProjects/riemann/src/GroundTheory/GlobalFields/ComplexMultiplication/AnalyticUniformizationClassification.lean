import Mathlib
import GroundTheory.GlobalFields.ComplexMultiplication.AnalyticUniformization
set_option maxSynthPendingDepth 1

open Complex Filter Topology Set WeierstrassCurve GroundTheory.Arith.Abelian
open scoped PeriodPair

noncomputable section

namespace GroundTheory.Global
namespace Elliptic

theorem vcPoint_mul_apply (C D : VariableChange ℂ) {W W' W'' : WeierstrassCurve ℂ}
    (hD : D • W = W') (hC : C • W' = W'') (P : W.toAffine.Point) :
    vcPoint (C * D) (by rw [mul_smul, hD, hC]) P = vcPoint C hC (vcPoint D hD P) := by
  rcases P with _ | ⟨x, y, h⟩
  · rfl
  · rw [vcPoint_some, vcPoint_some, vcPoint_some, Affine.Point.some.injEq]
    simp only [vcX, vcY, VariableChange.mul_def, mul_inv, Units.val_mul]
    have h1 : (D.u : ℂ) ≠ 0 := Units.ne_zero _
    have h2 : (C.u : ℂ) ≠ 0 := Units.ne_zero _
    simp only [Units.val_inv_eq_inv_val]
    constructor
    · field_simp
      ring
    · field_simp
      ring

theorem vcPoint_inv_vcPoint (C : VariableChange ℂ) {W W' : WeierstrassCurve ℂ} (h : C • W = W')
    (P : W.toAffine.Point) :
    vcPoint C⁻¹ (by rw [← h, inv_smul_smul]) (vcPoint C h P) = P := by
  rw [← vcPoint_mul_apply]
  rcases P with _ | ⟨x, y, h'⟩
  · rfl
  · rw [vcPoint_some, Affine.Point.some.injEq]
    simp [vcX, vcY, VariableChange.one_def]

theorem vcPoint_congr {C C' : VariableChange ℂ} (e : C = C') {W W' : WeierstrassCurve ℂ}
    (h : C • W = W') (h' : C' • W = W') (P : W.toAffine.Point) : vcPoint C h P = vcPoint C' h' P := by
  subst e
  rfl

section Coordinates

variable {W : WeierstrassCurve ℂ}

def ptX : W.toAffine.Point → ℂ
  | .zero => 0
  | .some x _ _ => x

def ptY : W.toAffine.Point → ℂ
  | .zero => 0
  | .some _ y _ => y

theorem exists_eq_some_ptX_ptY {P : W.toAffine.Point} (hP : P ≠ 0) :
    ∃ h : W.toAffine.Nonsingular (ptX P) (ptY P), P = .some (ptX P) (ptY P) h := by
  rcases P with _ | ⟨x, y, h⟩
  · exact absurd rfl hP
  · exact ⟨h, rfl⟩

end Coordinates

section Core

variable {L L' : PeriodPair} {g : ℂ →+ (weierstrassCurve L').toAffine.Point}

theorem IsAnalyticUniformization.analyticAt_ptX_ptY (hg : IsAnalyticUniformization L.lattice g)
    {z : ℂ} (hz : z ∉ L.lattice) :
    AnalyticAt ℂ (fun w ↦ ptX (g w)) z ∧ AnalyticAt ℂ (fun w ↦ ptY (g w)) z := by
  obtain ⟨X, Y, hX, hY, hev⟩ := hg.analyticAt_affine z (fun h ↦ hz ((hg.map_eq_zero_iff z).1 h))
  refine ⟨hX.congr ?_, hY.congr ?_⟩ <;> filter_upwards [hev] with w ⟨h, e⟩ <;> rw [e] <;> rfl

theorem IsAnalyticUniformization.exists_chart (hg : IsAnalyticUniformization L.lattice g)
    {z : ℂ} (hz : z ∈ L.lattice) :
    ∃ U V : ℂ → ℂ, AnalyticAt ℂ U z ∧ AnalyticAt ℂ V z ∧ U z = 0 ∧ V z = 0 ∧
      ∀ᶠ w in 𝓝[≠] z, V w ≠ 0 ∧ ptX (g w) = U w / V w ∧ ptY (g w) = 1 / V w := by
  obtain ⟨U, V, hU, hV, hev⟩ := hg.analyticAt_infinity z ((hg.map_eq_zero_iff z).2 hz)
  have h0 : U z = 0 ∧ V z = 0 := by
    rcases hev.self_of_nhds with ⟨_, hU0, hV0⟩ | ⟨_, _, e⟩
    · exact ⟨hU0, hV0⟩
    · exact absurd (e.symm.trans ((hg.map_eq_zero_iff z).2 hz)) (Affine.Point.some_ne_zero _)
  refine ⟨U, V, hU, hV, h0.1, h0.2, ?_⟩
  have hL : ∀ᶠ w in 𝓝[≠] z, w ∉ L.lattice := by
    rw [eventually_nhdsWithin_iff]
    filter_upwards [L.compl_lattice_sdiff_singleton_mem_nhds z] with w hw hwz hwL
    exact hw ⟨hwL, hwz⟩
  filter_upwards [nhdsWithin_le_nhds hev, hL] with w hw hwL
  rcases hw with ⟨hg0, -, -⟩ | ⟨hV0, h, e⟩
  · exact absurd ((hg.map_eq_zero_iff w).1 hg0) hwL
  · rw [e]
    exact ⟨hV0, rfl, rfl⟩

theorem IsAnalyticUniformization.meromorphic_ptX (hg : IsAnalyticUniformization L.lattice g) :
    Meromorphic fun w ↦ ptX (g w) := fun z ↦ by
  by_cases hz : z ∈ L.lattice
  · obtain ⟨U, V, hU, hV, -, -, hev⟩ := hg.exists_chart hz
    exact (hU.meromorphicAt.div hV.meromorphicAt).congr (by
      filter_upwards [hev] with w hw
      exact hw.2.1.symm)
  · exact (hg.analyticAt_ptX_ptY hz).1.meromorphicAt

theorem IsAnalyticUniformization.meromorphic_ptY (hg : IsAnalyticUniformization L.lattice g) :
    Meromorphic fun w ↦ ptY (g w) := fun z ↦ by
  by_cases hz : z ∈ L.lattice
  · obtain ⟨U, V, hU, hV, -, -, hev⟩ := hg.exists_chart hz
    exact (analyticAt_const.meromorphicAt.div hV.meromorphicAt).congr (by
      filter_upwards [hev] with w hw
      exact hw.2.2.symm)
  · exact (hg.analyticAt_ptX_ptY hz).2.meromorphicAt

theorem IsAnalyticUniformization.map_add_mem (hg : IsAnalyticUniformization L.lattice g) (z : ℂ)
    {l : ℂ} (hl : l ∈ L.lattice) : g (z + l) = g z := by
  rw [map_add, (hg.map_eq_zero_iff l).2 hl, add_zero]

theorem IsAnalyticUniformization.equation_ptX_ptY (hg : IsAnalyticUniformization L.lattice g)
    {z : ℂ} (hz : z ∉ L.lattice) :
    ptY (g z) ^ 2 = ptX (g z) ^ 3 + (weierstrassCurve L').a₄ * ptX (g z) + (weierstrassCurve L').a₆ := by
  obtain ⟨h, -⟩ := exists_eq_some_ptX_ptY (fun h0 ↦ hz ((hg.map_eq_zero_iff z).1 h0))
  have e := (Affine.equation_iff _ _).1 h.1
  simp only [weierstrassCurve_a₁, weierstrassCurve_a₂, weierstrassCurve_a₃, zero_mul, add_zero] at e
  rw [e]

end Core

section Omega

variable {L L' : PeriodPair} {g : ℂ →+ (weierstrassCurve L').toAffine.Point}

def omegaFun (g : ℂ →+ (weierstrassCurve L').toAffine.Point) (z : ℂ) : ℂ :=
  deriv (fun w ↦ ptX (g w)) z / (2 * ptY (g z))

theorem IsAnalyticUniformization.deriv_relation (hg : IsAnalyticUniformization L.lattice g) {z : ℂ}
    (hz : z ∉ L.lattice) : ∀ᶠ w in 𝓝 z, 2 * ptY (g w) * deriv (fun v ↦ ptY (g v)) w =
      (3 * ptX (g w) ^ 2 + (weierstrassCurve L').a₄) * deriv (fun v ↦ ptX (g v)) w := by
  have hO := L.isClosed_lattice.isOpen_compl
  filter_upwards [hO.mem_nhds hz] with w (hw : w ∉ L.lattice)
  obtain ⟨hX, hY⟩ := hg.analyticAt_ptX_ptY hw
  have e : (fun v ↦ ptX (g v) * ptX (g v) * ptX (g v) + (weierstrassCurve L').a₄ * ptX (g v) +
      (weierstrassCurve L').a₆) =ᶠ[𝓝 w] fun v ↦ ptY (g v) * ptY (g v) := by
    filter_upwards [hO.mem_nhds hw] with v (hv : v ∉ L.lattice)
    have := hg.equation_ptX_ptY hv
    linear_combination -this
  have hX' := hX.differentiableAt.hasDerivAt
  have hY' := hY.differentiableAt.hasDerivAt
  have h1 := hY'.mul hY'
  have h2 := (((hX'.mul hX').mul hX').add (hX'.const_mul (weierstrassCurve L').a₄)).add_const
    (weierstrassCurve L').a₆
  have := h1.unique (h2.congr_of_eventuallyEq e.symm)
  simp only [Pi.mul_apply] at this
  linear_combination this

theorem IsAnalyticUniformization.omegaFun_order_nonneg_of_notMem
    (hg : IsAnalyticUniformization L.lattice g) {z : ℂ} (hz : z ∉ L.lattice) :
    0 ≤ meromorphicOrderAt (omegaFun g) z := by
  obtain ⟨hX, hY⟩ := hg.analyticAt_ptX_ptY hz
  by_cases hY0 : ptY (g z) = 0
  · obtain ⟨h, -⟩ := exists_eq_some_ptX_ptY (fun h0 ↦ hz ((hg.map_eq_zero_iff z).1 h0))
    have hD : 3 * ptX (g z) ^ 2 + (weierstrassCurve L').a₄ ≠ 0 := by
      have h' := ((Affine.nonsingular_iff' _ _).1 h).2
      simp only [weierstrassCurve_a₁, weierstrassCurve_a₂, weierstrassCurve_a₃, hY0, zero_mul,
        mul_zero, add_zero, zero_sub, ne_eq, neg_eq_zero, not_true_eq_false, or_false] at h'
      exact h'
    set T : ℂ → ℂ := fun w ↦ deriv (fun v ↦ ptY (g v)) w /
      (3 * ptX (g w) ^ 2 + (weierstrassCurve L').a₄)
    have hT : AnalyticAt ℂ T z := hY.deriv.div (by fun_prop) hD
    have hDev : ∀ᶠ w in 𝓝 z, 3 * ptX (g w) ^ 2 + (weierstrassCurve L').a₄ ≠ 0 :=
      ((continuousAt_const.mul (hX.continuousAt.pow 2)).add continuousAt_const).eventually_ne hD
    have key : omegaFun g =ᶠ[𝓝[≠] z] T := by
      rcases hY.eventually_eq_zero_or_eventually_ne_zero with h0 | hne
      · have hd : ∀ᶠ w in 𝓝 z, deriv (fun v ↦ ptY (g v)) w = 0 := by
          filter_upwards [h0.eventually_nhds] with w hw
          have hw' : (fun v ↦ ptY (g v)) =ᶠ[𝓝 w] fun _ ↦ (0 : ℂ) := hw
          rw [hw'.deriv_eq]
          exact deriv_const w 0
        filter_upwards [nhdsWithin_le_nhds h0, nhdsWithin_le_nhds hd] with w hw hdw
        simp only [omegaFun, T, hw, hdw, mul_zero, div_zero, zero_div]
      · filter_upwards [hne, nhdsWithin_le_nhds (hg.deriv_relation hz), nhdsWithin_le_nhds hDev]
          with w hw hrel hDw
        simp only [omegaFun, T]
        rw [div_eq_div_iff (mul_ne_zero two_ne_zero hw) hDw]
        linear_combination -hrel
    rw [meromorphicOrderAt_congr key]
    exact hT.meromorphicOrderAt_nonneg
  · exact (hX.deriv.div (analyticAt_const.mul hY) (mul_ne_zero two_ne_zero hY0)).meromorphicOrderAt_nonneg

end Omega

section OmegaLattice

variable {L L' : PeriodPair} {g : ℂ →+ (weierstrassCurve L').toAffine.Point}

theorem IsAnalyticUniformization.omegaFun_order_nonneg_of_mem
    (hg : IsAnalyticUniformization L.lattice g) {z : ℂ} (hz : z ∈ L.lattice) :
    0 ≤ meromorphicOrderAt (omegaFun g) z := by
  obtain ⟨U, V, hU, hV, hU0, hV0, hev⟩ := hg.exists_chart hz
  set X : ℂ → ℂ := fun w ↦ ptX (g w) with hXdef
  set Y : ℂ → ℂ := fun w ↦ ptY (g w) with hYdef
  set a₄ := (weierstrassCurve L').a₄
  set a₆ := (weierstrassCurve L').a₆
  have hXm : MeromorphicAt X z := hg.meromorphic_ptX z
  have hYm : MeromorphicAt Y z := hg.meromorphic_ptY z

  have hVne : ∀ᶠ w in 𝓝[≠] z, V w ≠ 0 := hev.mono fun _ h ↦ h.1
  have oVtop : meromorphicOrderAt V z ≠ ⊤ :=
    (meromorphicOrderAt_ne_top_iff_eventually_ne_zero hV.meromorphicAt).2 hVne
  have oVpos : 0 < meromorphicOrderAt V z := by
    rw [← tendsto_zero_iff_meromorphicOrderAt_pos hV.meromorphicAt]
    have := hV.continuousAt.tendsto
    rw [hV0] at this
    exact this.mono_left nhdsWithin_le_nhds
  obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.1 oVtop
  have kpos : 0 < k := by
    rw [← hk] at oVpos
    exact_mod_cast oVpos

  have oY : meromorphicOrderAt Y z = ((-k : ℤ) : WithTop ℤ) := by
    have e : Y =ᶠ[𝓝[≠] z] V⁻¹ := by
      filter_upwards [hev] with w hw
      rw [Pi.inv_apply, ← one_div]
      exact hw.2.2
    rw [meromorphicOrderAt_congr e, meromorphicOrderAt_inv, ← hk]
    norm_cast

  have hgne : ∀ᶠ w in 𝓝[≠] z, w ∉ L.lattice := by
    filter_upwards [hev] with w hw hwL
    have h0 := (hg.map_eq_zero_iff w).2 hwL
    have h1 : ptY (g w) = 0 := by rw [h0]; rfl
    rw [hw.2.2] at h1
    exact one_div_ne_zero hw.1 h1
  have heq : (fun w ↦ Y w ^ 2) =ᶠ[𝓝[≠] z] fun w ↦ X w ^ 3 + a₄ * X w + a₆ := by
    filter_upwards [hgne] with w hw
    exact hg.equation_ptX_ptY hw
  have oY2 : meromorphicOrderAt (fun w ↦ Y w ^ 2) z = ((-(2 * k) : ℤ) : WithTop ℤ) := by
    show meromorphicOrderAt (Y ^ 2) z = _
    have e2 : ((2 : ℕ) : WithTop ℤ) = ((2 : ℤ) : WithTop ℤ) := by norm_cast
    rw [meromorphicOrderAt_pow hYm, oY, e2, ← WithTop.coe_mul]
    congr 1
    ring

  have hXneg : meromorphicOrderAt X z < 0 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨G, hG, hXG⟩ := hXm.meromorphicOrderAt_nonneg_iff.1 hcon
    have e2 : (fun w ↦ Y w ^ 2) =ᶠ[𝓝[≠] z] fun w ↦ G w ^ 3 + a₄ * G w + a₆ := by
      filter_upwards [heq, hXG] with w h1 h2
      rw [h1, h2]
    have h2 : 0 ≤ meromorphicOrderAt (fun w ↦ Y w ^ 2) z := by
      rw [meromorphicOrderAt_congr e2]
      exact (by fun_prop : AnalyticAt ℂ (fun w ↦ G w ^ 3 + a₄ * G w + a₆) z).meromorphicOrderAt_nonneg
    rw [oY2] at h2
    have : (0 : ℤ) ≤ -(2 * k) := by exact_mod_cast h2
    omega
  obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.1 (ne_top_of_lt hXneg)
  have mneg : m < 0 := by
    rw [← hm] at hXneg
    exact_mod_cast hXneg

  have h1 : (m : WithTop ℤ) ≤ meromorphicOrderAt (fun w ↦ a₄ * X w) z := by
    show (m : WithTop ℤ) ≤ meromorphicOrderAt ((fun _ ↦ a₄) * X) z
    rw [meromorphicOrderAt_mul (MeromorphicAt.const a₄ z) hXm, ← hm]
    have := (analyticAt_const (v := a₄) (x := z)).meromorphicOrderAt_nonneg
    calc (m : WithTop ℤ) = 0 + m := (zero_add _).symm
      _ ≤ _ := add_le_add this le_rfl
  have h2 : (m : WithTop ℤ) ≤ meromorphicOrderAt (fun _ ↦ a₆) z :=
    le_trans (by exact_mod_cast mneg.le) analyticAt_const.meromorphicOrderAt_nonneg
  have hH : MeromorphicAt (fun w ↦ a₄ * X w + a₆) z := by fun_prop
  have h3 : (m : WithTop ℤ) ≤ meromorphicOrderAt (fun w ↦ a₄ * X w + a₆) z := by
    show (m : WithTop ℤ) ≤ meromorphicOrderAt ((fun w ↦ a₄ * X w) + fun _ ↦ a₆) z
    exact le_trans (le_min h1 h2) (meromorphicOrderAt_add (by fun_prop) (MeromorphicAt.const _ _))
  have oX3 : meromorphicOrderAt (fun w ↦ X w ^ 3) z = ((3 * m : ℤ) : WithTop ℤ) := by
    show meromorphicOrderAt (X ^ 3) z = _
    rw [meromorphicOrderAt_pow hXm, ← hm]
    norm_cast
  have oRHS : meromorphicOrderAt (fun w ↦ X w ^ 3 + a₄ * X w + a₆) z = ((3 * m : ℤ) : WithTop ℤ) := by
    have e : (fun w ↦ X w ^ 3 + a₄ * X w + a₆) = (fun w ↦ X w ^ 3) + fun w ↦ a₄ * X w + a₆ := by
      funext w; simp only [Pi.add_apply]; ring
    have hlt : meromorphicOrderAt (fun w ↦ X w ^ 3) z < meromorphicOrderAt (fun w ↦ a₄ * X w + a₆) z := by
      rw [oX3]
      exact lt_of_lt_of_le (by exact_mod_cast (by omega : 3 * m < m)) h3
    rw [e, meromorphicOrderAt_add_eq_left_of_lt hH hlt, oX3]
  have hkm : 3 * m = -(2 * k) := by
    have := (meromorphicOrderAt_congr heq).symm.trans oY2
    rw [oRHS] at this
    exact_mod_cast this

  have oX' : meromorphicOrderAt (deriv X) z = ((m - 1 : ℤ) : WithTop ℤ) :=
    meromorphicOrderAt_deriv_eq_sub_one (by exact_mod_cast mneg.ne) hm.symm
  have o2Y : meromorphicOrderAt (fun w ↦ 2 * Y w) z = ((-k : ℤ) : WithTop ℤ) := by
    show meromorphicOrderAt ((fun _ ↦ (2 : ℂ)) * Y) z = _
    rw [meromorphicOrderAt_mul_of_ne_zero analyticAt_const two_ne_zero, oY]
  have e : omegaFun g = deriv X * (fun w ↦ 2 * Y w)⁻¹ := by
    funext w
    simp only [omegaFun, Pi.mul_apply, Pi.inv_apply, div_eq_mul_inv]
    rfl
  rw [e, meromorphicOrderAt_mul hXm.deriv (show MeromorphicAt (fun w ↦ 2 * Y w) z by fun_prop).inv,
    meromorphicOrderAt_inv, oX', o2Y]
  have : (0 : ℤ) ≤ m - 1 + k := by omega
  have e' : (((m - 1 : ℤ) : WithTop ℤ) + -((-k : ℤ) : WithTop ℤ)) = ((m - 1 + k : ℤ) : WithTop ℤ) := by
    norm_cast
    ring
  rw [e']
  exact_mod_cast this

end OmegaLattice

section Lift

variable {L L' : PeriodPair} {g : ℂ →+ (weierstrassCurve L').toAffine.Point}

theorem eq_of_eventuallyEq_codiscrete {f₁ f₂ : ℂ → ℂ} {z : ℂ} (h : f₁ =ᶠ[codiscrete ℂ] f₂)
    (h₁ : ContinuousAt f₁ z) (h₂ : ContinuousAt f₂ z) : f₁ z = f₂ z := by
  have h' : ∀ᶠ w in 𝓝[≠] z, f₁ w = f₂ w := by
    have := (mem_codiscreteWithin_iff_forall_mem_nhdsNE.1 h) z (mem_univ z)
    rw [compl_univ, union_empty] at this
    exact this
  exact tendsto_nhds_unique ((h₁.tendsto.mono_left nhdsWithin_le_nhds).congr' h')
    (h₂.tendsto.mono_left nhdsWithin_le_nhds)

theorem IsAnalyticUniformization.meromorphic_omegaFun (hg : IsAnalyticUniformization L.lattice g) :
    Meromorphic (omegaFun g) := fun z ↦
  ((hg.meromorphic_ptX z).deriv).div ((MeromorphicAt.const 2 z).mul (hg.meromorphic_ptY z))

theorem IsAnalyticUniformization.isPeriodic_omegaFun (hg : IsAnalyticUniformization L.lattice g) :
    IsPeriodic L (omegaFun g) := by
  intro z l hl
  have hX : (fun w ↦ ptX (g (w + l))) = fun w ↦ ptX (g w) := funext fun w ↦ by rw [hg.map_add_mem w hl]
  simp only [omegaFun, hg.map_add_mem z hl]
  congr 1
  rw [← deriv_comp_add_const, hX]

theorem IsAnalyticUniformization.exists_omegaFun_eq_const (hg : IsAnalyticUniformization L.lattice g) :
    ∃ α : ℂ, omegaFun g =ᶠ[codiscrete ℂ] fun _ ↦ α :=
  exists_eventuallyEq_const_of_meromorphicOrderAt_nonneg L hg.meromorphic_omegaFun hg.isPeriodic_omegaFun
    fun z ↦ by
      by_cases hz : z ∈ L.lattice
      · exact hg.omegaFun_order_nonneg_of_mem hz
      · exact hg.omegaFun_order_nonneg_of_notMem hz

theorem IsAnalyticUniformization.ptY_eq_zero_of_two_mul_mem (hg : IsAnalyticUniformization L.lattice g)
    {z : ℂ} (hz : z ∉ L.lattice) (h2 : 2 * z ∈ L.lattice) : ptY (g z) = 0 := by
  obtain ⟨h, e⟩ := exists_eq_some_ptX_ptY (fun h0 ↦ hz ((hg.map_eq_zero_iff z).1 h0))
  have h0 : g z + g z = 0 := by rw [← map_add, ← two_mul]; exact (hg.map_eq_zero_iff _).2 h2
  have hneg : g z = -g z := eq_neg_of_add_eq_zero_left h0
  rw [e, Affine.Point.neg_some, Affine.Point.some.injEq] at hneg
  have := hneg.2
  simp only [Affine.negY, weierstrassCurve_a₁, weierstrassCurve_a₃, zero_mul, sub_zero] at this
  linear_combination this / 2

theorem IsAnalyticUniformization.two_mul_mem_of_ptY_eq_zero (hg : IsAnalyticUniformization L.lattice g)
    {z : ℂ} (hz : z ∉ L.lattice) (hY : ptY (g z) = 0) : 2 * z ∈ L.lattice := by
  obtain ⟨h, e⟩ := exists_eq_some_ptX_ptY (fun h0 ↦ hz ((hg.map_eq_zero_iff z).1 h0))
  have hneg : -g z = g z := by
    rw [e, Affine.Point.neg_some, Affine.Point.some.injEq]
    refine ⟨rfl, ?_⟩
    simp only [Affine.negY, weierstrassCurve_a₁, weierstrassCurve_a₃, zero_mul, sub_zero, hY, neg_zero]
  rw [← hg.map_eq_zero_iff, two_mul, map_add]
  nth_rewrite 1 [← hneg]
  exact neg_add_cancel _

theorem IsAnalyticUniformization.eventually_ptY_ne_zero (hg : IsAnalyticUniformization L.lattice g) :
    ∀ᶠ z in codiscrete ℂ, ptY (g z) ≠ 0 := by
  filter_upwards [eventually_affine (eventually_notMem_lattice L) two_ne_zero 0] with z hz hY
  rw [add_zero] at hz
  have hz' : z ∉ L.lattice := fun h ↦ hz (by rw [two_mul]; exact add_mem h h)
  exact hz (hg.two_mul_mem_of_ptY_eq_zero hz' hY)

theorem IsAnalyticUniformization.eventually_equation (hg : IsAnalyticUniformization L.lattice g) :
    ∀ᶠ z in codiscrete ℂ, (weierstrassCurve L').toAffine.Equation (ptX (g z)) (ptY (g z)) := by
  filter_upwards [eventually_notMem_lattice L] with z hz
  obtain ⟨h, -⟩ := exists_eq_some_ptX_ptY (fun h0 ↦ hz ((hg.map_eq_zero_iff z).1 h0))
  exact h.1

theorem IsAnalyticUniformization.not_eventually_ptX_eq_const
    (hg : IsAnalyticUniformization L.lattice g) (c : ℂ) :
    ¬ (fun z ↦ ptX (g z)) =ᶠ[codiscrete ℂ] fun _ ↦ c := by
  intro h
  have half : ∀ z, z ∉ L.lattice → 2 * z ∈ L.lattice → g z = g (L.ω₁ / 2) := by
    have key : ∀ z, z ∉ L.lattice → 2 * z ∈ L.lattice →
        ∃ hn, g z = .some c 0 hn := by
      intro z hz h2
      obtain ⟨hn, e⟩ := exists_eq_some_ptX_ptY (fun h0 ↦ hz ((hg.map_eq_zero_iff z).1 h0))
      have hx : ptX (g z) = c :=
        eq_of_eventuallyEq_codiscrete h (hg.analyticAt_ptX_ptY hz).1.continuousAt continuousAt_const
      have hy : ptY (g z) = 0 := hg.ptY_eq_zero_of_two_mul_mem hz h2
      rw [e]
      exact exists_point_some_eq hn hx.symm hy.symm |>.imp fun _ h ↦ h
    intro z hz h2
    obtain ⟨h₁, e₁⟩ := key z hz h2
    obtain ⟨h₂, e₂⟩ := key (L.ω₁ / 2) L.ω₁_div_two_notMem_lattice (by
      rw [mul_div_cancel₀ _ two_ne_zero]; exact L.ω₁_mem_lattice)
    rw [e₁, e₂]
  have e := half (L.ω₂ / 2) L.ω₂_div_two_notMem_lattice (by
    rw [mul_div_cancel₀ _ two_ne_zero]; exact L.ω₂_mem_lattice)
  have hmem : L.ω₂ / 2 - L.ω₁ / 2 ∈ L.lattice := by
    rw [← hg.map_eq_zero_iff, map_sub, e, sub_self]
  have := (PeriodPair.mul_ω₁_add_mul_ω₂_mem_lattice (L := L) (α := -1 / 2) (β := 1 / 2)).1 (by
    convert hmem using 1
    push_cast
    ring)
  norm_num at this

theorem IsAnalyticUniformization.exists_mul_add (hg : IsAnalyticUniformization L.lattice g) :
    ∃ α c : ℂ, α ≠ 0 ∧
      (fun z ↦ ptX (g z)) =ᶠ[codiscrete ℂ] (fun z ↦ ℘[L'] (α * z + c)) ∧
      (fun z ↦ ptY (g z)) =ᶠ[codiscrete ℂ] (fun z ↦ ℘'[L'] (α * z + c) / 2) := by
  obtain ⟨α, hα⟩ := hg.exists_omegaFun_eq_const
  set X : ℂ → ℂ := fun z ↦ ptX (g z) with hXdef
  set Y : ℂ → ℂ := fun z ↦ ptY (g z) with hYdef
  have hXm : Meromorphic X := hg.meromorphic_ptX
  have hYm : Meromorphic Y := hg.meromorphic_ptY
  have hPn : ((weierstrassCurve L').baseChange MeroField).toAffine.Nonsingular (germ X) (germ Y) :=
    Affine.equation_iff_nonsingular.1 (equation_germ hXm hYm hg.eventually_equation)
  have hYne : germ Y ≠ 0 := by
    intro h
    rw [germ_eq_zero_iff hYm] at h
    obtain ⟨z, h1, h2⟩ := nonempty_of_mem_codiscrete (h.and hg.eventually_ptY_ne_zero)
    exact h2 h1
  have h2ne : (2 : MeroField) ≠ 0 := by
    rw [← map_ofNat (algebraMap ℂ MeroField) 2]
    exact (_root_.map_ne_zero _).2 two_ne_zero
  have h2Y : (2 : MeroField) * germ Y ≠ 0 := mul_ne_zero h2ne hYne
  have hderiv : germ (deriv X) = 2 * germ Y * algebraMap ℂ MeroField α := by
    have e : deriv X =ᶠ[codiscrete ℂ] fun z ↦ 2 * Y z * α := by
      filter_upwards [hα, hg.eventually_ptY_ne_zero] with z h1 h2
      simp only [omegaFun] at h1
      rw [div_eq_iff (mul_ne_zero two_ne_zero h2)] at h1
      rw [h1]
      ring
    have hm : Meromorphic fun z ↦ 2 * Y z * α := fun z ↦ by fun_prop
    rw [(germ_eq_germ_iff hXm.deriv hm).2 e,
      show (fun z ↦ 2 * Y z * α) = ((fun _ ↦ (2 : ℂ)) * Y) * fun _ ↦ α from rfl,
      germ_mul ((Meromorphic.const 2).mul hYm) (Meromorphic.const α),
      germ_mul (Meromorphic.const 2) hYm, germ_const, germ_const, map_ofNat]
  have hω : omegaDeriv (omegaAt (weierstrassCurve L') (.some _ _ hPn)) = algebraMap ℂ MeroField α := by
    obtain ⟨s₁, -⟩ := omegaAt_some_spec (weierstrassCurve L') hPn
    have e := congrArg omegaDeriv s₁
    rw [LinearMap.map_smul, omegaDeriv_D, germDeriv_germ hXm] at e
    simp only [WeierstrassCurve.baseChange, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₃,
      weierstrassCurve_a₁, weierstrassCurve_a₃, map_zero, zero_mul, add_zero, smul_eq_mul] at e
    rw [hderiv] at e
    exact mul_left_cancel₀ h2Y e
  have hα0 : α ≠ 0 := by
    rintro rfl
    rw [map_zero, mul_zero] at hderiv
    rw [← germDeriv_germ hXm] at hderiv
    obtain ⟨c, hc⟩ := exists_eq_algebraMap_of_germDeriv_eq_zero hderiv
    rw [← germ_const, germ_eq_germ_iff hXm (Meromorphic.const c)] at hc
    exact hg.not_eventually_ptX_eq_const c hc
  have hD : omegaDeriv (omegaAt (weierstrassCurve L')
      ((.some _ _ hPn : ((weierstrassCurve L').baseChange MeroField).toAffine.Point) -
        affinePoint L' α 0 hα0)) = 0 := by
    have h1 : omegaAt (weierstrassCurve L') ((.some _ _ hPn : ((weierstrassCurve L').baseChange
        MeroField).toAffine.Point) - affinePoint L' α 0 hα0) =
        omegaAt (weierstrassCurve L') (.some _ _ hPn) - omegaAt (weierstrassCurve L') (affinePoint L' α 0 hα0) :=
      map_sub (omegaHom (weierstrassCurve L')) _ _
    rw [h1, map_sub, hω, omegaDeriv_affinePoint, sub_self]
  obtain ⟨R, hR⟩ := exists_eq_constMap_of_omegaDeriv _ hD
  obtain ⟨c, rfl⟩ := toPoint_surjective (L := L') R
  have hP : (.some _ _ hPn : ((weierstrassCurve L').baseChange MeroField).toAffine.Point) =
      affinePoint L' α (0 + c) hα0 := by
    rw [← affinePoint_add_constMap, ← hR]
    abel
  rw [zero_add] at hP
  simp only [affinePoint, Affine.Point.some.injEq] at hP
  refine ⟨α, c, hα0, ?_, ?_⟩
  · exact (germ_eq_germ_iff hXm (meromorphic_weierstrassP_affine L' α c)).1 hP.1
  · exact (germ_eq_germ_iff hYm (meromorphic_derivWeierstrassP_half_affine L' α c)).1 hP.2

end Lift

section Classification

theorem exists_mul_of_isAnalyticUniformization {L L' : PeriodPair}
    {g : ℂ →+ (weierstrassCurve L').toAffine.Point} (hg : IsAnalyticUniformization L.lattice g) :
    ∃ α : ℂ, α ≠ 0 ∧ (∀ z, z ∈ L.lattice ↔ α * z ∈ L'.lattice) ∧ ∀ z, g z = toPoint L' (α * z) := by
  obtain ⟨α, c, hα, hX, hY⟩ := hg.exists_mul_add
  have good : ∀ z, z ∉ L.lattice → α * z + c ∉ L'.lattice → g z = toPoint L' (α * z + c) := by
    intro z hz hz'
    obtain ⟨hn, e⟩ := exists_eq_some_ptX_ptY (fun h0 ↦ hz ((hg.map_eq_zero_iff z).1 h0))
    obtain ⟨hXa, hYa⟩ := hg.analyticAt_ptX_ptY hz
    have haff : ContinuousAt (fun w ↦ α * w + c) z := by fun_prop
    have hx : ptX (g z) = ℘[L'] (α * z + c) := eq_of_eventuallyEq_codiscrete hX hXa.continuousAt
      ((L'.analyticOnNhd_weierstrassP _ hz').continuousAt.comp_of_eq haff rfl)
    have hy : ptY (g z) = ℘'[L'] (α * z + c) / 2 := eq_of_eventuallyEq_codiscrete hY hYa.continuousAt
      (((L'.analyticOnNhd_derivWeierstrassP _ hz').continuousAt.comp_of_eq haff rfl).div_const 2)
    rw [e, toPoint_of_notMem hz']
    exact point_some_congr hx hy
  have hG : ∀ᶠ w in codiscrete ℂ, w ∉ L.lattice ∧ α * w + c ∉ L'.lattice :=
    (eventually_notMem_lattice L).and (eventually_affine (eventually_notMem_lattice L') hα c)
  have all : ∀ z, g z = toPoint L' (α * z + 2 * c) := by
    intro z
    obtain ⟨w, ⟨hw1, hw2⟩, hw3, hw4⟩ :=
      nonempty_of_mem_codiscrete (hG.and (eventually_affine hG (neg_ne_zero.2 one_ne_zero) z))
    have e : z = w + (-1 * w + z) := by ring
    rw [e, map_add, good w hw1 hw2, good _ hw3 hw4, ← toPoint_add]
    congr 1
    ring
  obtain ⟨w, hw1, hw2⟩ := nonempty_of_mem_codiscrete hG
  have hc : c ∈ L'.lattice := by
    have e := (good w hw1 hw2).symm.trans (all w)
    have := torusToPoint_injective (L := L') (a₁ := Torus.mk L' _) (a₂ := Torus.mk L' _) e
    rw [Torus.mk_eq_mk_iff] at this
    convert neg_mem this using 1
    ring
  have all' : ∀ z, g z = toPoint L' (α * z) := fun z ↦ by
    rw [all z, toPoint_add_mem (by rw [two_mul]; exact add_mem hc hc)]
  refine ⟨α, hα, fun z ↦ ?_, all'⟩
  rw [← hg.map_eq_zero_iff, all', toPoint_eq_zero_iff]

variable {E : WeierstrassCurve ℂ} [E.IsElliptic] {L : PeriodPair}

theorem exists_vcPoint_of_isAnalyticUniformization {f : ℂ →+ E.toAffine.Point}
    (hf : IsAnalyticUniformization L.lattice f) :
    ∃ (C : VariableChange ℂ) (h : C • weierstrassCurve L = E), ∀ z, f z = vcPoint C h (toPoint L z) := by
  obtain ⟨L', C', hC'⟩ := exists_variableChange_eq_weierstrassCurve E
  have hg := hf.vcPoint C' hC'
  obtain ⟨α, hα, hker, hgz⟩ := exists_mul_of_isAnalyticUniformization hg
  have hlat : (L'.lattice : Set ℂ) = (α * ·) '' L.lattice := by
    ext y
    constructor
    · intro hy
      refine ⟨α⁻¹ * y, (hker _).2 (by rw [mul_inv_cancel_left₀ hα]; exact hy), ?_⟩
      show α * (α⁻¹ * y) = y
      rw [mul_inv_cancel_left₀ hα]
    · rintro ⟨z, hz, rfl⟩
      exact (hker z).1 hz
  have hinv : C'⁻¹ • weierstrassCurve L' = E := by rw [← hC', inv_smul_smul]
  refine ⟨C'⁻¹ * scaleVC hα, by rw [mul_smul, scaleVC_smul hα hlat, hinv], fun z ↦ ?_⟩
  rw [vcPoint_mul_apply (C'⁻¹) (scaleVC hα) (scaleVC_smul hα hlat) hinv,
    vcPoint_scaleVC_toPoint hα hlat, ← hgz z]
  show f z = vcPoint C'⁻¹ hinv (vcPoint C' hC' (f z))
  exact (vcPoint_inv_vcPoint C' hC' (f z)).symm

theorem exists_mul_eq_of_isAnalyticUniformization {f₁ f₂ : ℂ →+ E.toAffine.Point}
    (hf₁ : IsAnalyticUniformization L.lattice f₁) (hf₂ : IsAnalyticUniformization L.lattice f₂) :
    ∃ c : ℂ, c ≠ 0 ∧ (∀ z, z ∈ L.lattice ↔ c * z ∈ L.lattice) ∧ ∀ z, f₂ z = f₁ (c * z) := by
  obtain ⟨C, hC, hf₁C⟩ := exists_vcPoint_of_isAnalyticUniformization hf₁
  have hinv : C⁻¹ • E = weierstrassCurve L := by rw [← hC, inv_smul_smul]
  have hg := hf₂.vcPoint C⁻¹ hinv
  obtain ⟨c, hc, hker, hgz⟩ := exists_mul_of_isAnalyticUniformization hg
  refine ⟨c, hc, hker, fun z ↦ ?_⟩
  have e := hgz z
  rw [AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom, vcPointEquiv_apply] at e
  rw [hf₁C, ← e]
  have := vcPoint_inv_vcPoint C⁻¹ hinv (f₂ z)
  rw [vcPoint_congr (inv_inv C) _ hC] at this
  exact this.symm

end Classification

end Elliptic
end GroundTheory.Global
