import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

open Topology ValuativeRel

namespace GlobalTheory.CjInv

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {w : Pl E}

theorem valuation_equiv :
    (valuation (w.adicCompletion E)).IsEquiv (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ))) := by
  haveI : (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  exact isEquiv _ _

theorem lt_one_iff (x : w.adicCompletion E) : valuation (w.adicCompletion E) x < 1 ↔ Valued.v x < 1 := by
  simp only [← not_le]
  exact not_congr valuation_equiv.one_le_iff_one_le

theorem tendsto_pow_zero {x : w.adicCompletion E} (h : Valued.v x < 1) :
    Tendsto (fun n : ℕ => x ^ n) atTop (𝓝 0) := by
  rw [← lt_one_iff] at h
  rw [(IsValuativeTopology.hasBasis_nhds_zero' (w.adicCompletion E)).tendsto_right_iff]
  intro γ hγ
  have : MulArchimedean (ValueGroupWithZero (w.adicCompletion E)) :=
    ValuativeRel.isRankLeOne_iff_mulArchimedean.mp inferInstance
  obtain ⟨n, hn⟩ := exists_pow_lt₀ h (Units.mk0 γ hγ)
  filter_upwards [eventually_ge_atTop n] with m hm
  show valuation _ (x ^ m) < γ
  rw [map_pow]
  exact lt_of_le_of_lt (pow_le_pow_right_of_le_one' h.le hm) hn

theorem lt_one_mem_nhds : {y : w.adicCompletion E | Valued.v y < 1} ∈ 𝓝 (0 : w.adicCompletion E) := by
  have := (IsValuativeTopology.hasBasis_nhds_zero' (w.adicCompletion E)).mem_iff.2 ⟨1, one_ne_zero, fun _ hy => hy⟩
  simpa only [lt_one_iff] using this

theorem lt_one_of_map (s : w.adicCompletion E →+* w.adicCompletion E) (hs : Continuous s) {x : w.adicCompletion E}
    (h : Valued.v x < 1) : Valued.v (s x) < 1 := by
  have h1 : Tendsto (fun n : ℕ => s x ^ n) atTop (𝓝 0) := by
    have := (hs.tendsto 0).comp (tendsto_pow_zero h)
    simpa [Function.comp_def, map_pow] using this
  obtain ⟨N, hN⟩ := (h1.eventually lt_one_mem_nhds).exists
  by_contra hc
  push_neg at hc
  have : 1 ≤ Valued.v (s x ^ N) := by rw [map_pow]; exact one_le_pow₀ hc
  exact absurd hN (not_lt.2 this)

theorem le_exp_neg_one {x : WithZero (Multiplicative ℤ)} (hx : x < 1) : x ≤ WithZero.exp (-1) := by
  by_cases h0 : x = 0
  · rw [h0]; exact zero_le'
  · rw [← WithZero.exp_log h0] at hx ⊢
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at hx
    rw [WithZero.exp_le_exp]
    omega

theorem valued_map_eq (s : w.adicCompletion E →+* w.adicCompletion E) (hs : Continuous s) (hss : ∀ x, s (s x) = x)
    (x : w.adicCompletion E) : Valued.v (s x) = Valued.v x := by

  have hle : ∀ y : w.adicCompletion E, Valued.v y ≤ 1 → Valued.v (s y) ≤ 1 := by
    intro y hy
    by_contra hc
    push_neg at hc
    have hy0 : s y ≠ 0 := by
      intro h0; rw [h0, map_zero] at hc; exact absurd hc (not_lt.2 zero_le')
    have h1 : Valued.v (s y)⁻¹ < 1 := by rw [map_inv₀]; exact inv_lt_one_of_one_lt₀ hc
    have h2 := lt_one_of_map s hs h1
    rw [map_inv₀, hss, map_inv₀] at h2
    have h0 : (0 : WithZero (Multiplicative ℤ)) < Valued.v y := by
      rw [zero_lt_iff, Valuation.ne_zero_iff]
      intro h; apply hy0; rw [h, map_zero]
    exact absurd hy (not_le.2 ((inv_lt_one₀ h0).1 h2))

  have hord : ∀ a b : w.adicCompletion E, b ≠ 0 → Valued.v a ≤ Valued.v b → Valued.v (s a) ≤ Valued.v (s b) := by
    intro a b hb hab
    have hb' : s b ≠ 0 := (map_ne_zero s).2 hb
    have h1 : Valued.v (a / b) ≤ 1 := by
      rw [map_div₀]; exact div_le_one_of_le₀ hab zero_le'
    have h2 := hle _ h1
    rw [map_div₀, map_div₀] at h2
    have h0 : (0 : WithZero (Multiplicative ℤ)) < Valued.v (s b) := by
      rw [zero_lt_iff, Valuation.ne_zero_iff]; exact hb'
    exact (div_le_one₀ h0).1 h2

  obtain ⟨π, hπ⟩ := w.valuation_exists_uniformizer E
  set p : w.adicCompletion E := algebraMap E (w.adicCompletion E) π with hp
  have hvp : Valued.v p = WithZero.exp (-1) := by
    have := HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w π
    rw [hπ] at this
    exact this
  have hp0 : p ≠ 0 := by
    intro h; rw [h, map_zero] at hvp; exact WithZero.exp_ne_zero hvp.symm
  have hsp0 : s p ≠ 0 := (map_ne_zero s).2 hp0
  have hvsp : Valued.v (s p) = Valued.v p := by
    apply le_antisymm
    · rw [hvp]; apply le_exp_neg_one; apply lt_one_of_map s hs; rw [hvp]
      rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num
    · have := hord (s p) p hp0 (by
        rw [hvp]; apply le_exp_neg_one; apply lt_one_of_map s hs; rw [hvp]
        rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num)
      rwa [hss] at this
  by_cases hx : x = 0
  · rw [hx, map_zero]
  have hvx : Valued.v x ≠ 0 := (Valuation.ne_zero_iff _).2 hx
  set k := WithZero.log (Valued.v x) with hk
  set u := x * p ^ k with hu
  have hvpk : Valued.v p ^ k ≠ 0 := zpow_ne_zero _ ((Valuation.ne_zero_iff _).2 hp0)
  have hvu : Valued.v u = 1 := by
    rw [hu, map_mul, map_zpow₀, hvp, ← WithZero.exp_log hvx, ← hk, ← WithZero.exp_zsmul, ← WithZero.exp_add]
    simp
  have hu0 : u ≠ 0 := by
    intro h; rw [h, map_zero] at hvu; exact zero_ne_one hvu
  have hsu1 : Valued.v (s u) ≤ 1 := hle u hvu.le
  have hsu2 : Valued.v (s u⁻¹) ≤ 1 := hle u⁻¹ (by rw [map_inv₀, hvu, inv_one])
  have hsu : Valued.v (s u) = 1 := by
    apply le_antisymm hsu1
    rw [map_inv₀, map_inv₀] at hsu2
    have h0 : (0 : WithZero (Multiplicative ℤ)) < Valued.v (s u) := by
      rw [zero_lt_iff, Valuation.ne_zero_iff]; exact (map_ne_zero s).2 hu0
    exact (inv_le_one₀ h0).1 hsu2
  rw [hu, map_mul, map_zpow₀, map_mul, map_zpow₀, hvsp] at hsu
  rw [hu, map_mul, map_zpow₀] at hvu
  exact mul_right_cancel₀ hvpk (hsu.trans hvu.symm)

end GlobalTheory.CjInv

namespace GlobalTheory.BCT

theorem cj_involutive_valuation : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E),
    (∀ x, cj w (cj w x) = x) ∧ ∀ x, Valued.v (cj w x) = Valued.v x := by
  intro E _ _ _ w
  have key : (∀ x, cj w (cj w x) = x) ∧ Continuous (cj w) := by
    unfold cj
    split_ifs with h
    · obtain ⟨hc, hE⟩ := h.choose_spec
      refine ⟨fun x => ?_, hc⟩
      have hd := HeightOneSpectrum.denseRange_algebraMap E w
      have := hd.equalizer (hc.comp hc) continuous_id (funext fun y => by
        simp only [Function.comp_apply, id_eq, hE, IsCMField.complexConj_apply_apply])
      exact congrFun this x
    · exact ⟨fun x => rfl, continuous_id⟩
  exact ⟨key.1, GlobalTheory.CjInv.valued_map_eq (cj w) key.2 key.1⟩

end GlobalTheory.BCT
