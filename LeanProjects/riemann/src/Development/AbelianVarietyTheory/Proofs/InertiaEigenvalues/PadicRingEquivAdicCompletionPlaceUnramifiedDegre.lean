import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroTypeInertia
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RestrictMem
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.LocalLanglandsGL
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousRingEquivLocalFieldPreservesValuation
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
open NumberField IsDedekindDomain Polynomial ValuativeRel

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LocalFieldIso

theorem resCard_padic (g : ℕ) [Fact g.Prime] : GlobalTheory.SplitWeil.resCard ℚ_[g] = g := by
  let e : 𝒪[ℚ_[g]] ≃+* ℤ_[g] :=
  { toFun := fun x => ⟨x.1, by
      have h := (Valuation.mem_integer_iff _ _).1 x.2
      have := (GlobalTheory.SplitWeil.padic_valuation_lt_iff g 1 x.1).not.1 (by rw [map_one]; exact not_lt.2 h)
      rwa [norm_one, not_lt] at this⟩
    invFun := fun x => ⟨x.1, (Valuation.mem_integer_iff _ _).2 (by
      have := (GlobalTheory.SplitWeil.padic_valuation_lt_iff g 1 x.1).not.2 (by rw [norm_one]; exact not_lt.2 x.2)
      rwa [map_one, not_lt] at this)⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    map_mul' := fun _ _ => rfl
    map_add' := fun _ _ => rfl }
  unfold GlobalTheory.SplitWeil.resCard
  rw [Nat.card_congr ((IsLocalRing.ResidueField.mapEquiv e).trans PadicInt.residueField).toEquiv, Nat.card_zmod]

theorem padic_v_map_le_one_iff {E : Type} [Field E] [NumberField E] {g : ℕ} [Fact g.Prime]
    {w : HeightOneSpectrum (𝓞 E)} (i : ℚ_[g] ≃+* w.adicCompletion E) (hi : Continuous i) (y : ℚ_[g]) :
    Valued.v (i y) ≤ 1 ↔ ‖y‖ ≤ 1 := by
  haveI : (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  rw [← (ValuativeRel.isEquiv (ValuativeRel.valuation _) Valued.v).le_one_iff_le_one,
    valuation_map_le_one_iff i hi y]
  have := (GlobalTheory.SplitWeil.padic_valuation_lt_iff g 1 y).not
  rwa [map_one, norm_one, not_lt, not_lt] at this

end GlobalTheory.LocalFieldIso

open GlobalTheory.LocalFieldIso in

theorem GlobalTheory.LocalFieldIso.padic_iso_place : ∀ (E : Type) [Field E] [NumberField E] (g : ℕ) [Fact g.Prime] (w : HeightOneSpectrum (𝓞 E))
    (i : ℚ_[g] ≃+* w.adicCompletion E), Continuous i →
    ((g : ℕ) : 𝓞 E) ∈ w.asIdeal ∧ ((g : ℕ) : 𝓞 E) ∉ w.asIdeal ^ 2 ∧ Formalism.ConjugateSelfDual.normV w = g := by
  intro E _ _ g _ w i hi
  have hv : ∀ y : E, Valued.v (algebraMap E (w.adicCompletion E) y) = w.valuation E y := fun y =>
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w y
  have hgc : i (g : ℚ_[g]) = algebraMap E (w.adicCompletion E) (((g : ℕ) : 𝓞 E) : E) := by simp
  have hgp : 1 < (g : ℝ) := by exact_mod_cast (Fact.out : g.Prime).one_lt
  refine ⟨?_, ?_, ?_⟩
  · have h := GlobalTheory.Published.DepthZeroTypeModel.v_lt_one i hi (k := (g : ℚ_[g])) Padic.norm_p_lt_one
    rw [hgc, hv, HeightOneSpectrum.valuation_of_algebraMap] at h
    rwa [HeightOneSpectrum.intValuation_lt_one_iff_mem] at h
  · intro hg2
    have h2 := (HeightOneSpectrum.intValuation_le_pow_iff_mem w _ 2).2 hg2
    obtain ⟨π, hπ⟩ := HeightOneSpectrum.valuation_exists_uniformizer E w
    set P := algebraMap E (w.adicCompletion E) π with hP
    have hPv : Valued.v P = WithZero.exp (-1) := by rw [hP, hv, hπ]
    have hP0 : P ≠ 0 := by intro h; rw [h, map_zero] at hPv; exact WithZero.exp_ne_zero hPv.symm
    set x := i.symm P with hx
    have hix : i x = P := by simp [hx]
    have hx0 : x ≠ 0 := by intro h; apply hP0; rw [← hix, h, map_zero]
    have hxlt : ‖x‖ < 1 := by
      by_contra hc
      have h1 : ‖x⁻¹‖ ≤ 1 := by rw [norm_inv]; exact inv_le_one_of_one_le₀ (not_lt.1 hc)
      have h3 := (padic_v_map_le_one_iff i hi _).2 h1
      rw [map_inv₀, hix, map_inv₀, hPv, ← WithZero.exp_neg, neg_neg] at h3
      exact absurd h3 (not_le.2 (by rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num))
    have hxle : ‖x‖ ≤ (g : ℝ) ^ (-1 : ℤ) :=
      (Padic.norm_le_pow_iff_norm_lt_pow_add_one x (-1)).2 (by simpa using hxlt)
    have hy : Valued.v (i ((g : ℚ_[g]) * x⁻¹ ^ 2)) ≤ 1 := by
      rw [map_mul, hgc, map_pow, map_inv₀, hix, Valuation.map_mul, hv, HeightOneSpectrum.valuation_of_algebraMap,
        Valuation.map_pow, map_inv₀, hPv]
      refine le_trans (mul_le_mul_of_nonneg_right h2 zero_le') (le_of_eq ?_)
      rw [← WithZero.exp_neg, ← WithZero.exp_nsmul, ← WithZero.exp_add]
      norm_num
    have hn := (padic_v_map_le_one_iff i hi _).1 hy
    rw [norm_mul, norm_pow, norm_inv, Padic.norm_p] at hn
    have hxpos : 0 < ‖x‖ := norm_pos_iff.2 hx0
    have : (g : ℝ)⁻¹ ≤ ‖x‖ ^ 2 := by
      rwa [inv_pow, ← div_eq_mul_inv, div_le_one (by positivity)] at hn
    rw [zpow_neg_one] at hxle
    have hg0 : (0 : ℝ) < (g : ℝ)⁻¹ := by positivity
    have h5 : ‖x‖ ^ 2 ≤ ((g : ℝ)⁻¹) ^ 2 := pow_le_pow_left₀ hxpos.le hxle 2
    have h6 : ((g : ℝ)⁻¹) ^ 2 < (g : ℝ)⁻¹ := by
      rw [sq]; exact mul_lt_of_lt_one_left hg0 (inv_lt_one_of_one_lt₀ hgp)
    linarith
  · rw [← GlobalTheory.LocLanglands.resCard_eq_normV, resCard_eq i hi, resCard_padic]
