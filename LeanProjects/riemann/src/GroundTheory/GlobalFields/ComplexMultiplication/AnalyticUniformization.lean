import Mathlib
import GroundTheory.GlobalFields.ComplexMultiplication.ClassGroupActionIso
import GroundTheory.GlobalFields.ComplexMultiplication.JInvariantHomothety
import GroundTheory.GlobalFields.ComplexMultiplication.EllipticConstant
set_option maxSynthPendingDepth 1

open Complex Filter Topology Set WeierstrassCurve GroundTheory.Arith.Abelian
open scoped PeriodPair

noncomputable section

namespace GroundTheory.Global
namespace Elliptic

structure IsAnalyticUniformization (Λ : Submodule ℤ ℂ) {E : WeierstrassCurve ℂ}
    (f : ℂ →+ E.toAffine.Point) : Prop where
  map_eq_zero_iff : ∀ z, f z = 0 ↔ z ∈ Λ
  surjective : Function.Surjective f
  analyticAt_affine : ∀ z, f z ≠ 0 → ∃ X Y : ℂ → ℂ, AnalyticAt ℂ X z ∧ AnalyticAt ℂ Y z ∧
    ∀ᶠ w in 𝓝 z, ∃ h : E.toAffine.Nonsingular (X w) (Y w), f w = .some (X w) (Y w) h
  analyticAt_infinity : ∀ z, f z = 0 → ∃ U V : ℂ → ℂ, AnalyticAt ℂ U z ∧ AnalyticAt ℂ V z ∧
    ∀ᶠ w in 𝓝 z, (f w = 0 ∧ U w = 0 ∧ V w = 0) ∨
      (V w ≠ 0 ∧ ∃ h : E.toAffine.Nonsingular (U w / V w) (1 / V w),
        f w = .some (U w / V w) (1 / V w) h)

section Lattice

variable (L : PeriodPair)

theorem meromorphicOrderAt_derivWeierstrassP {z : ℂ} (hz : z ∈ L.lattice) :
    meromorphicOrderAt ℘'[L] z = -3 := by
  have h := meromorphicOrderAt_deriv_eq_sub_one (f := ℘[L]) (x := z) (n := -2)
    (by norm_num) (by rw [L.order_weierstrassP z hz]; rfl)
  rw [L.deriv_weierstrassP] at h
  rw [h]
  rfl

theorem limPunctured_eq_zero_of_pos {f : ℂ → ℂ} {z : ℂ}
    (ho : 0 < meromorphicOrderAt f z) : limPunctured f z = 0 := by
  have hf : MeromorphicAt f z := by
    by_contra h
    rw [meromorphicOrderAt_of_not_meromorphicAt h] at ho
    exact lt_irrefl _ ho
  exact tendsto_nhds_unique (tendsto_limPunctured hf ho.le) (tendsto_zero_of_meromorphicOrderAt_pos ho)

theorem isAnalyticUniformization_toPointHom :
    IsAnalyticUniformization L.lattice (toPointHom L) where
  map_eq_zero_iff z := toPoint_eq_zero_iff
  surjective := toPoint_surjective
  analyticAt_affine z hz := by
    have hz' : z ∉ L.lattice := fun h ↦ hz (toPoint_of_mem h)
    refine ⟨℘[L], fun w ↦ ℘'[L] w / 2, L.analyticOnNhd_weierstrassP z hz',
      (L.analyticOnNhd_derivWeierstrassP z hz').div_const, ?_⟩
    filter_upwards [L.isClosed_lattice.isOpen_compl.mem_nhds hz'] with w hw
    exact ⟨_, toPoint_of_notMem hw⟩
  analyticAt_infinity z hz := by
    have hzL : z ∈ L.lattice := toPoint_eq_zero_iff.1 hz
    set F : ℂ → ℂ := fun w ↦ ℘[L] w / (℘'[L] w / 2)
    set G : ℂ → ℂ := fun w ↦ 1 / (℘'[L] w / 2)
    have hP := L.meromorphic_weierstrassP z
    have hD : MeromorphicAt (fun w ↦ ℘'[L] w / 2) z := (L.meromorphic_derivWeierstrassP z).div
      (MeromorphicAt.const 2 z)
    have oD : meromorphicOrderAt (fun w ↦ ℘'[L] w / 2) z = -3 := by
      have e : (fun w ↦ ℘'[L] w / 2) = (fun _ ↦ (2 : ℂ)⁻¹) * ℘'[L] := by
        funext w; simp only [Pi.mul_apply]; ring
      rw [e, meromorphicOrderAt_mul_of_ne_zero analyticAt_const (by norm_num),
        meromorphicOrderAt_derivWeierstrassP L hzL]
    have hF : MeromorphicAt F z := hP.div hD
    have hG : MeromorphicAt G z := (MeromorphicAt.const 1 z).div hD
    have oF : meromorphicOrderAt F z = 1 := by
      rw [show F = ℘[L] * (fun w ↦ ℘'[L] w / 2)⁻¹ from funext fun w ↦ div_eq_mul_inv _ _,
        meromorphicOrderAt_mul hP hD.inv, meromorphicOrderAt_inv, oD,
        L.order_weierstrassP z hzL]
      rfl
    have oG : meromorphicOrderAt G z = 3 := by
      rw [show G = (fun w ↦ ℘'[L] w / 2)⁻¹ from funext fun w ↦ one_div _,
        meromorphicOrderAt_inv, oD]
      rfl
    have hFz : limPunctured F z = 0 := limPunctured_eq_zero_of_pos (by rw [oF]; exact zero_lt_one)
    have hGz : limPunctured G z = 0 := limPunctured_eq_zero_of_pos (by rw [oG]; norm_num)
    refine ⟨limPunctured F, limPunctured G,
      analyticAt_limPunctured hF (by rw [oF]; exact zero_le_one),
      analyticAt_limPunctured hG (by rw [oG]; norm_num), ?_⟩
    have hne : ∀ᶠ w in 𝓝[≠] z, w ∉ L.lattice ∧ ℘'[L] w / 2 ≠ 0 := by
      refine (eventually_nhdsWithin_iff.2 ?_).and
        ((meromorphicOrderAt_ne_top_iff_eventually_ne_zero hD).1 (by rw [oD]; decide))
      filter_upwards [L.compl_lattice_sdiff_singleton_mem_nhds z] with w hw hwz hwL
      exact hw ⟨hwL, hwz⟩
    rw [eventually_nhdsWithin_iff] at hne
    filter_upwards [hne] with w hw
    by_cases hwz : w = z
    · subst hwz
      exact Or.inl ⟨hz, hFz, hGz⟩
    obtain ⟨hwL, hw0⟩ := hw hwz
    have hDa : AnalyticAt ℂ (fun w ↦ ℘'[L] w / 2) w :=
      (L.analyticOnNhd_derivWeierstrassP w hwL).div_const
    have hFw : limPunctured F w = F w := limPunctured_eq_of_continuousAt
      ((L.analyticOnNhd_weierstrassP w hwL).div hDa hw0).continuousAt
    have hGw : limPunctured G w = G w := limPunctured_eq_of_continuousAt
      (analyticAt_const.div hDa hw0).continuousAt
    have hGne : G w ≠ 0 := one_div_ne_zero hw0
    have hw0' : ℘'[L] w ≠ 0 := fun h ↦ hw0 (by rw [h, zero_div])
    have e1 : F w / G w = ℘[L] w := by
      simp only [F, G]; field_simp
    have e2 : 1 / G w = ℘'[L] w / 2 := by
      simp only [G]; field_simp
    refine Or.inr ⟨by rw [hGw]; exact hGne, ?_⟩
    rw [hFw, hGw]
    refine ⟨by rw [e1, e2]; exact WeierstrassCurve.Affine.equation_iff_nonsingular.1 (equation_weierstrassP L hwL), ?_⟩
    show toPoint L w = _
    rw [toPoint_of_notMem hwL]
    exact point_some_congr e1.symm e2.symm

end Lattice

section VariableChange

theorem exists_point_some_eq {W : WeierstrassCurve ℂ} {x y x' y' : ℂ} (h : W.toAffine.Nonsingular x y)
    (ex : x' = x) (ey : y' = y) :
    ∃ h' : W.toAffine.Nonsingular x' y', (Affine.Point.some x y h : W.toAffine.Point) = .some x' y' h' := by
  subst ex; subst ey; exact ⟨h, rfl⟩

variable {Λ : Submodule ℤ ℂ} {E E' : WeierstrassCurve ℂ} {f : ℂ →+ E.toAffine.Point}

theorem IsAnalyticUniformization.vcPoint (hf : IsAnalyticUniformization Λ f) (C : VariableChange ℂ)
    (h : C • E = E') : IsAnalyticUniformization Λ ((vcPointEquiv C h).toAddMonoidHom.comp f) where
  map_eq_zero_iff z := by
    rw [AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom, vcPointEquiv_apply, vcPoint_eq_zero_iff,
      hf.map_eq_zero_iff]
  surjective := (vcPointEquiv C h).surjective.comp hf.surjective
  analyticAt_affine z hz := by
    have hz' : f z ≠ 0 := fun h0 ↦ hz (by
      rw [AddMonoidHom.comp_apply, h0, map_zero])
    obtain ⟨X, Y, hX, hY, hev⟩ := hf.analyticAt_affine z hz'
    refine ⟨fun w ↦ vcX C (X w), fun w ↦ vcY C (X w) (Y w), ?_, ?_, ?_⟩
    · simp only [vcX]; fun_prop
    · simp only [vcY]; fun_prop
    filter_upwards [hev] with w ⟨hw, e⟩
    rw [AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom, vcPointEquiv_apply, e, vcPoint_some]
    exact ⟨_, rfl⟩
  analyticAt_infinity z hz := by
    have hz' : f z = 0 := by
      rw [AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom, vcPointEquiv_apply,
        vcPoint_eq_zero_iff] at hz
      exact hz
    obtain ⟨U, V, hU, hV, hev⟩ := hf.analyticAt_infinity z hz'
    have h0 : U z = 0 ∧ V z = 0 := by
      rcases hev.self_of_nhds with ⟨-, hU0, hV0⟩ | ⟨-, h1, e⟩
      · exact ⟨hU0, hV0⟩
      · exact absurd (e.symm.trans hz') (Affine.Point.some_ne_zero _)
    set v : ℂ := ((C.u⁻¹ : ℂˣ) : ℂ)
    have hv : v ≠ 0 := Units.ne_zero _
    set D : ℂ → ℂ := fun w ↦ 1 - C.s * U w + C.s * C.r * V w - C.t * V w
    have hD : AnalyticAt ℂ D z := by simp only [D]; fun_prop
    have hDz : D z = 1 := by simp only [D, h0.1, h0.2]; ring
    have hDne : ∀ᶠ w in 𝓝 z, D w ≠ 0 :=
      hD.continuousAt.eventually_ne (by rw [hDz]; exact one_ne_zero)
    refine ⟨fun w ↦ (U w - C.r * V w) / (v * D w), fun w ↦ V w / (v ^ 3 * D w), ?_, ?_, ?_⟩
    · exact (hU.sub (analyticAt_const.mul hV)).div (analyticAt_const.mul hD)
        (mul_ne_zero hv (by rw [hDz]; exact one_ne_zero))
    · exact hV.div (analyticAt_const.mul hD) (mul_ne_zero (pow_ne_zero 3 hv) (by rw [hDz]; exact one_ne_zero))
    filter_upwards [hev, hDne] with w hw hDw
    rw [AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom, vcPointEquiv_apply]
    rcases hw with ⟨hf0, hU0, hV0⟩ | ⟨hV0, hw, e⟩
    · left
      rw [hf0]
      exact ⟨rfl, by rw [hU0, hV0]; simp, by rw [hV0]; simp⟩
    · right
      refine ⟨div_ne_zero hV0 (mul_ne_zero (pow_ne_zero 3 hv) hDw), ?_⟩
      rw [e, vcPoint_some]
      apply exists_point_some_eq
      · simp only [vcX]
        field_simp
        ring
      · simp only [vcY, D]
        field_simp
        ring

end VariableChange

theorem IsAnalyticUniformization.comp_mul {Λ Λ' : Submodule ℤ ℂ} {E : WeierstrassCurve ℂ}
    {f : ℂ →+ E.toAffine.Point} (hf : IsAnalyticUniformization Λ f) {c : ℂ} (hc : c ≠ 0)
    (hΛ : ∀ z, z ∈ Λ' ↔ c * z ∈ Λ) :
    IsAnalyticUniformization Λ' (f.comp (AddMonoidHom.mulLeft c)) where
  map_eq_zero_iff z := by
    rw [AddMonoidHom.comp_apply, AddMonoidHom.coe_mulLeft, hf.map_eq_zero_iff, hΛ]
  surjective P := by
    obtain ⟨y, rfl⟩ := hf.surjective P
    exact ⟨c⁻¹ * y, by rw [AddMonoidHom.comp_apply, AddMonoidHom.coe_mulLeft, mul_inv_cancel_left₀ hc]⟩
  analyticAt_affine z hz := by
    obtain ⟨X, Y, hX, hY, hev⟩ := hf.analyticAt_affine (c * z) hz
    have ht : Tendsto (fun w ↦ c * w) (𝓝 z) (𝓝 (c * z)) := (continuous_const_mul c).tendsto z
    refine ⟨fun w ↦ X (c * w), fun w ↦ Y (c * w), hX.comp_of_eq (by fun_prop) rfl,
      hY.comp_of_eq (by fun_prop) rfl, ?_⟩
    filter_upwards [ht.eventually hev] with w hw
    exact hw
  analyticAt_infinity z hz := by
    obtain ⟨U, V, hU, hV, hev⟩ := hf.analyticAt_infinity (c * z) hz
    have ht : Tendsto (fun w ↦ c * w) (𝓝 z) (𝓝 (c * z)) := (continuous_const_mul c).tendsto z
    refine ⟨fun w ↦ U (c * w), fun w ↦ V (c * w), hU.comp_of_eq (by fun_prop) rfl,
      hV.comp_of_eq (by fun_prop) rfl, ?_⟩
    filter_upwards [ht.eventually hev] with w hw
    exact hw

section Homothety

variable {L L' : PeriodPair} {c : ℂ}

def latticeScaleEquiv (hc : c ≠ 0) (h : (L'.lattice : Set ℂ) = (c * ·) '' L.lattice) :
    L.lattice ≃ L'.lattice :=
  have hmem : ∀ l ∈ L.lattice, c * l ∈ L'.lattice := fun l hl ↦ by
    have : c * l ∈ (L'.lattice : Set ℂ) := by rw [h]; exact ⟨l, hl, rfl⟩
    exact this
  have hmem' : ∀ l ∈ L'.lattice, c⁻¹ * l ∈ L.lattice := fun l hl ↦ by
    have : l ∈ (c * ·) '' (L.lattice : Set ℂ) := by rw [← h]; exact hl
    obtain ⟨m, hm, rfl⟩ := this
    rwa [inv_mul_cancel_left₀ hc]
  { toFun := fun l ↦ ⟨c * l, hmem _ l.2⟩
    invFun := fun l ↦ ⟨c⁻¹ * l, hmem' _ l.2⟩
    left_inv := fun l ↦ by ext; simp [hc]
    right_inv := fun l ↦ by ext; simp [hc] }

theorem mem_lattice_iff_of_scale (hc : c ≠ 0) (h : (L'.lattice : Set ℂ) = (c * ·) '' L.lattice)
    (z : ℂ) : c * z ∈ L'.lattice ↔ z ∈ L.lattice := by
  constructor
  · intro hz
    exact (by simpa [latticeScaleEquiv, hc] using
      ((latticeScaleEquiv hc h).symm ⟨c * z, hz⟩).2 : z ∈ L.lattice)
  · intro hz
    exact ((latticeScaleEquiv hc h) ⟨z, hz⟩).2

theorem weierstrassP_scale (hc : c ≠ 0) (h : (L'.lattice : Set ℂ) = (c * ·) '' L.lattice) (z : ℂ) :
    ℘[L'] (c * z) = (c ^ 2)⁻¹ * ℘[L] z := by
  rw [PeriodPair.weierstrassP, PeriodPair.weierstrassP, ← (latticeScaleEquiv hc h).tsum_eq,
    ← tsum_mul_left]
  refine tsum_congr fun l ↦ ?_
  show 1 / (c * z - c * (l : ℂ)) ^ 2 - 1 / (c * (l : ℂ)) ^ 2 = (c ^ 2)⁻¹ * (1 / (z - l) ^ 2 - 1 / (l : ℂ) ^ 2)
  rw [← mul_sub, mul_pow, mul_pow, one_div, one_div, one_div, one_div, mul_inv, mul_inv, mul_sub]

theorem derivWeierstrassP_scale (hc : c ≠ 0) (h : (L'.lattice : Set ℂ) = (c * ·) '' L.lattice)
    (z : ℂ) : ℘'[L'] (c * z) = (c ^ 3)⁻¹ * ℘'[L] z := by
  rw [PeriodPair.derivWeierstrassP, PeriodPair.derivWeierstrassP, ← (latticeScaleEquiv hc h).tsum_eq,
    mul_neg, ← tsum_mul_left]
  congr 1
  refine tsum_congr fun l ↦ ?_
  show 2 / (c * z - c * (l : ℂ)) ^ 3 = (c ^ 3)⁻¹ * (2 / (z - l) ^ 3)
  rw [← mul_sub, mul_pow, div_eq_mul_inv, div_eq_mul_inv, mul_inv]
  ring

def scaleVC (hc : c ≠ 0) : VariableChange ℂ := ⟨Units.mk0 c hc, 0, 0, 0⟩

theorem scaleVC_smul (hc : c ≠ 0) (h : (L'.lattice : Set ℂ) = (c * ·) '' L.lattice) :
    scaleVC hc • weierstrassCurve L = weierstrassCurve L' := by
  have h4 := G_eq_of_lattice_eq_smul hc h 4
  have h6 := G_eq_of_lattice_eq_smul hc h 6
  ext
  · simp [scaleVC, variableChange_a₁]
  · simp [scaleVC, variableChange_a₂]
  · simp [scaleVC, variableChange_a₃]
  · simp only [variableChange_a₄, scaleVC, weierstrassCurve_a₄, weierstrassCurve_a₁,
      weierstrassCurve_a₂, weierstrassCurve_a₃, PeriodPair.g₂, h4, Units.val_inv_eq_inv_val,
      Units.val_mk0]
    ring
  · simp only [variableChange_a₆, scaleVC, weierstrassCurve_a₆, weierstrassCurve_a₄,
      weierstrassCurve_a₁, weierstrassCurve_a₂, weierstrassCurve_a₃, PeriodPair.g₃, h6,
      Units.val_inv_eq_inv_val, Units.val_mk0]
    ring

theorem vcPoint_scaleVC_toPoint (hc : c ≠ 0) (h : (L'.lattice : Set ℂ) = (c * ·) '' L.lattice)
    (z : ℂ) : vcPoint (scaleVC hc) (scaleVC_smul hc h) (toPoint L z) = toPoint L' (c * z) := by
  by_cases hz : z ∈ L.lattice
  · rw [toPoint_of_mem hz, toPoint_of_mem ((mem_lattice_iff_of_scale hc h z).2 hz)]
    rfl
  · have hz' : c * z ∉ L'.lattice := fun h' ↦ hz ((mem_lattice_iff_of_scale hc h z).1 h')
    rw [toPoint_of_notMem hz, toPoint_of_notMem hz', vcPoint_some]
    apply point_some_congr
    · simp only [vcX, scaleVC, weierstrassP_scale hc h, Units.val_inv_eq_inv_val, Units.val_mk0,
        sub_zero]
      ring
    · simp only [vcY, scaleVC, derivWeierstrassP_scale hc h, Units.val_inv_eq_inv_val,
        Units.val_mk0, sub_zero, zero_mul]
      ring

end Homothety

end Elliptic
end GroundTheory.Global
