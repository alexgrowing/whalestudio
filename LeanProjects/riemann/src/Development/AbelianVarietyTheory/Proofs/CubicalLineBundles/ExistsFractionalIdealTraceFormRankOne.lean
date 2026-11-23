import Mathlib
import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsCoprimeTwoSubRtTwoAddRt
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsHermCoordOfDatum
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FinrankEqOfInjectiveOfSpan
import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.TraceFormDualOneTraceFormDual
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.OneMulConjFracOneEqInvDifferent
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.NatCardAlgHomEqFinrankOfIsReducedOfIsFractionRin

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

noncomputable section
namespace GlobalTheory.CM.RankOne

variable {E : Type} [Field E] [NumberField E]

theorem trace_eq_sum {Ω : Type} [Field Ω] [CharZero Ω] [Fintype (E →+* Ω)]
    (h : Nat.card (E →+* Ω) = Module.finrank ℚ E) (x : E) :
    ((Algebra.trace ℚ E x : ℚ) : Ω) = ∑ τ : E →+* Ω, τ x := by
  rw [← eq_ratCast (algebraMap ℚ Ω)]
  exact algebraMap_trace_eq_sum_algHom_of_card (Nat.card_eq_fintype_card.symm.trans h)
    (P := fun τ : E →+* Ω => τ.toRatAlgHom) (fun τ τ' e => RingHom.ext fun y => AlgHom.congr_fun e y) x

variable [IsCMField E]

theorem re_pos_of_trace_pos {β : E} (hβ : IsCMField.complexConj E β = β) (hβ0 : β ≠ 0)
    (h : ∀ x : E, x ≠ 0 → 0 < Algebra.trace ℚ E (β * x * IsCMField.complexConj E x)) (τ : E →+* ℂ) :
    0 < (τ β).re := by
  classical
  have him : ∀ σ : E →+* ℂ, (σ β).im = 0 := fun σ => by
    rw [← Complex.conj_eq_iff_im, ← IsCMField.complexEmbedding_complexConj, hβ]
  have hne : (τ β).re ≠ 0 := fun e => (map_ne_zero τ).2 hβ0 (Complex.ext e (him τ))
  refine lt_of_le_of_ne (not_lt.1 fun hneg => ?_) hne.symm
  obtain ⟨a, ha, hb⟩ := AbsoluteValue.exists_one_lt_lt_one_pi_of_not_isEquiv
    (v := fun v : InfinitePlace E => v.1) (fun v => v.isNontrivial)
    (fun _ _ h => (InfinitePlace.eq_iff_isEquiv (K := E)).not.mp h) (InfinitePlace.mk τ)
  replace ha : 1 < ‖τ a‖ := ha
  replace hb : ∀ σ : E →+* ℂ, InfinitePlace.mk σ ≠ InfinitePlace.mk τ → ‖σ a‖ < 1 := fun σ hσ => hb _ hσ
  have ha0 : a ≠ 0 := by
    rintro rfl
    norm_num at ha
  have h1 : ∀ n : ℕ, 0 < ∑ σ : E →+* ℂ, (σ β).re * (‖σ a‖ ^ 2) ^ n := fun n => by
    have h2 := congrArg Complex.re (trace_eq_sum (Ω := ℂ) (by rw [Nat.card_eq_fintype_card, Embeddings.card])
      (β * a ^ n * IsCMField.complexConj E (a ^ n)))
    have h3 : (0 : ℝ) < (Algebra.trace ℚ E (β * a ^ n * IsCMField.complexConj E (a ^ n)) : ℚ) := by
      exact_mod_cast h _ (pow_ne_zero n ha0)
    rw [Complex.ratCast_re, Complex.re_sum] at h2
    rw [h2] at h3
    convert h3 using 2 with σ
    rw [map_mul, map_mul, IsCMField.complexEmbedding_complexConj, _root_.mul_assoc, Complex.mul_conj,
      Complex.re_mul_ofReal, map_pow, map_pow, Complex.normSq_eq_norm_sq]
  let g : (E →+* ℂ) → ℕ → ℝ := fun σ n =>
    if InfinitePlace.mk σ = InfinitePlace.mk τ then (τ β).re else (σ β).re * (‖σ a‖ ^ 2) ^ n
  have h2 : ∀ n, 0 ≤ ∑ σ, g σ n := fun n => (h1 n).le.trans (Finset.sum_le_sum fun σ _ => by
    simp only [g]
    split_ifs with hσ
    · have e1 : ‖σ a‖ = ‖τ a‖ := congrArg (fun v : InfinitePlace E => v a) hσ
      have e2 : (σ β).re = (τ β).re := by
        rcases InfinitePlace.mk_eq_iff.1 hσ with rfl | rfl
        · rfl
        · simp
      rw [e1, e2]
      have e3 : 1 ≤ (‖τ a‖ ^ 2) ^ n := one_le_pow₀ (one_le_pow₀ ha.le)
      nlinarith
    · exact le_rfl)
  have h3 : Filter.Tendsto (fun n => ∑ σ, g σ n) Filter.atTop
      (nhds (∑ σ : E →+* ℂ, if InfinitePlace.mk σ = InfinitePlace.mk τ then (τ β).re else 0)) := by
    refine tendsto_finset_sum _ fun σ _ => ?_
    simp only [g]
    split_ifs with hσ
    · exact tendsto_const_nhds
    · simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (sq_nonneg ‖σ a‖)
        (pow_lt_one₀ (norm_nonneg _) (hb σ hσ) two_ne_zero)).const_mul (σ β).re
  refine absurd (ge_of_tendsto' h3 h2) (not_le.2 ?_)
  refine (Finset.sum_lt_sum (g := fun _ => 0) (fun σ _ => ?_) ⟨τ, Finset.mem_univ _, ?_⟩).trans_eq (by simp)
  · split_ifs
    · exact hneg.le
    · exact le_rfl
  · simpa using hneg

theorem log_absNorm_of_selfDual {𝔞 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E} (h𝔞 : 𝔞 ≠ 0) {c : E} (hc : c ≠ 0)
    (h : ∀ v, v ∈ 𝔞 ↔ ∀ y ∈ 𝔞, ∃ n : ℤ, Algebra.trace ℚ E (c * v * IsCMField.complexConj E y) = n) :
    2 * Real.log (FractionalIdeal.absNorm 𝔞 : ℚ) + Real.log |(Algebra.norm ℚ c : ℚ)| =
      -(Module.finrank ℚ E * Real.log (rootDiscr E)) := by
  have h0 := conjFrac_ne_zero h𝔞
  have h1 : FractionalIdeal.dual ℤ ℚ (conjFrac 𝔞) = FractionalIdeal.spanSingleton _ c * 𝔞 := by
    ext w
    obtain ⟨v, rfl⟩ : ∃ v, w = c * v := ⟨c⁻¹ * w, (mul_inv_cancel_left₀ hc w).symm⟩
    have : c * v ∈ FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 E)) c * 𝔞 ↔ v ∈ 𝔞 := by
      rw [FractionalIdeal.mem_singleton_mul]
      exact ⟨fun ⟨y, hy, e⟩ => mul_left_cancel₀ hc e ▸ hy, fun hv => ⟨v, hv, rfl⟩⟩
    rw [this, h, FractionalIdeal.mem_dual h0]
    constructor
    · intro hh y hy
      obtain ⟨n, hn⟩ := hh _ (cc_mem_conjFrac.2 hy)
      exact ⟨n, hn.symm⟩
    · intro hh y hy
      obtain ⟨n, hn⟩ := hh _ (mem_conjFrac.1 hy)
      refine ⟨n, ?_⟩
      rw [FD.cc, IsCMField.complexConj_apply_apply] at hn
      exact hn.symm
  rw [FractionalIdeal.dual_eq_mul_inv, ← inv_inv (FractionalIdeal.dual ℤ ℚ 1),
    ← coeIdeal_differentIdeal ℤ ℚ E (𝓞 E)] at h1
  have nz : ∀ {𝔞 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E}, 𝔞 ≠ 0 → (FractionalIdeal.absNorm 𝔞 : ℝ) ≠ 0 :=
    fun h => by simpa using h
  have h3 := congrArg (fun 𝔞 => Real.log (FractionalIdeal.absNorm 𝔞 : ℚ)) h1
  have hN : (Algebra.norm ℚ c : ℝ) ≠ 0 := by exact_mod_cast Algebra.norm_ne_zero_iff.2 hc
  have hd : (0 : ℝ) < (|discr E| : ℤ) := by exact_mod_cast abs_pos.2 (discr_ne_zero E)
  have h2 : (0 : ℝ) < Module.finrank ℚ E := by exact_mod_cast Module.finrank_pos
  simp only [map_mul, map_inv₀, Rat.cast_mul, Rat.cast_inv, FractionalIdeal.coeIdeal_absNorm,
    FractionalIdeal.absNorm_span_singleton, absNorm_differentIdeal E (𝓞 E), Rat.cast_natCast, Nat.cast_natAbs,
    Rat.cast_intCast] at h3
  rw [Real.log_mul (inv_ne_zero hd.ne') (inv_ne_zero (nz h0)), Real.log_inv, Real.log_inv,
    log_absNorm_conjFrac h𝔞, Real.log_mul (by simpa using hN) (nz h𝔞)] at h3
  rw [rootDiscr_def, Real.log_rpow hd, mul_inv_cancel_left₀ h2.ne', ← Rat.cast_abs]
  linarith

theorem coe_rt_eq (H : Host E) : (H.rt : E) = 2 * (H.w0 : E) - 1 := by
  rw [HostModel.rt_eq]; push_cast; rfl

theorem conj_rt (H : Host E) : IsCMField.complexConj E (H.rt : E) = -(H.rt : E) := by
  rw [← H.bar_eq, HostModel.bar_rt]; push_cast; rfl

theorem coe_rt_ne_zero (H : Host E) : (H.rt : E) ≠ 0 := by
  exact_mod_cast HostModel.rt_ne_zero H

theorem log_norm_rt (H : Host E) :
    Real.log |(Algebra.norm ℚ (H.rt : E) : ℚ)| = Module.finrank ℚ E * (Real.log H.d / 2) := by
  have h := congrArg (fun z : E => Real.log |(Algebra.norm ℚ z : ℚ)|) (HostModel.coe_sq_eq_neg H.rt_sq)
  have e : (-(H.d : E)) = algebraMap ℚ E (-(H.d : ℚ)) := by simp
  simp only [e, Algebra.norm_algebraMap, map_pow, Rat.cast_pow, Real.log_abs, Real.log_pow, Rat.cast_neg,
    Real.log_neg_eq_log, Rat.cast_natCast, Nat.cast_ofNat] at h
  rw [Real.log_abs]
  linarith

theorem relTrace_eq (H : Host E) {Ω : Type} [Field Ω] [CharZero Ω] (hΩ : Nat.card (E →+* Ω) = Module.finrank ℚ E)
    (τ₀ : E →+* Ω) (z : E) :
    ((Algebra.trace ℚ E (H.w0 * z / H.rt) : ℚ) : Ω) - (Algebra.trace ℚ E (z / H.rt) : ℚ) +
      (Algebra.trace ℚ E (z / H.rt) : ℚ) * τ₀ H.w0 =
      ∑ᶠ τ : {τ : E →+* Ω // τ (H.rt : E) = τ₀ (H.rt : E)}, τ.1 z := by
  classical
  have : Finite (E →+* Ω) := Nat.finite_of_card_ne_zero (by rw [hΩ]; exact Module.finrank_pos.ne')
  have := Fintype.ofFinite (E →+* Ω)
  rw [finsum_eq_sum_of_fintype, ← Finset.sum_subtype (Finset.univ.filter fun τ : E →+* Ω => τ (H.rt : E) = τ₀ (H.rt : E))
    (by simp) (fun τ : E →+* Ω => τ z), Finset.sum_filter, trace_eq_sum hΩ, trace_eq_sum hΩ, Finset.sum_mul,
    ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun τ _ => ?_
  have h0 : τ (H.rt : E) ≠ 0 := (map_ne_zero τ).2 (coe_rt_ne_zero H)
  have h1 : ∀ σ : E →+* Ω, σ (H.rt : E) = 2 * σ H.w0 - 1 := fun σ => by
    rw [coe_rt_eq, map_sub, map_mul, map_ofNat, map_one]
  have h2 : ∀ σ : E →+* Ω, σ (H.rt : E) ^ 2 = -(H.d : Ω) := fun σ => by
    rw [← map_pow, HostModel.coe_sq_eq_neg H.rt_sq, map_neg, map_natCast]
  have h3 := h1 τ
  have h4 := h1 τ₀
  simp only [map_div₀, map_mul]
  split_ifs with hτ
  · field_simp
    linear_combination (τ z / 2) * (- hτ - h3 - h4)
  · have h5 := (sq_eq_sq_iff_eq_or_eq_neg.1 ((h2 τ).trans (h2 τ₀).symm)).resolve_left hτ
    field_simp
    linear_combination (τ z / 2) * (h5 - h3 - h4)

end GlobalTheory.CM.RankOne

namespace GlobalTheory.CM

open RankOne

theorem exists_ideal_traceForm_of_rank_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (ε : ℤˣ) (h : D.La → D.La → OK H), D.p + D.q = 1 → IsKForm D ε h → (∀ x : D.La, x ≠ 0 → 0 < (ε : ℤ) * D.EF (H.w0 • x) x) → ∃ (𝔞 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (e : D.La →ₗ[𝓞 E] E) (β : E), 𝔞 ≠ 0 ∧ Function.Injective e ∧ LinearMap.range e = (𝔞 : Submodule (𝓞 E) E) ∧ IsCMField.complexConj E β = β ∧ (∀ τ : E →+* ℂ, 0 < (τ β).re) ∧
  (∀ (Ω : Type) [Field Ω] [CharZero Ω], Nat.card (E →+* Ω) = Module.finrank ℚ E → ∀ (τ₀ : E →+* Ω) x y, τ₀ (((h x y : OK H) : 𝓞 E) : E) = ∑ᶠ τ : {τ : E →+* Ω // τ (H.rt : E) = τ₀ (H.rt : E)}, τ.1 (β * e x * IsCMField.complexConj E (e y))) ∧
  2 * Real.log (FractionalIdeal.absNorm 𝔞 : ℚ) + Real.log |(Algebra.norm ℚ β : ℚ)| = Module.finrank ℚ E * (Real.log H.d / 2 - Real.log (NumberField.rootDiscr E)) := by
  intro E _ _ _ H D ε h hr hh hpos
  have hε : ((ε : ℤ) : E) * (ε : ℤ) = 1 := by
    rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]
  have hrt := coe_rt_ne_zero H
  have hε0 : ((ε : ℤ) : E) ≠ 0 := left_ne_zero_of_mul_eq_one hε
  have hξ : FD.cc (((ε : ℤ) : E) / H.rt) = -(((ε : ℤ) : E) / H.rt) := by
    rw [FD.cc, map_div₀, map_intCast, conj_rt, div_neg]
  obtain ⟨G, φ, hm⟩ := exists_herm_coord_of_datum E H D _ hξ (div_ne_zero hε0 hrt) 1 hr.symm
  obtain ⟨-, hfg, -, hdual⟩ := HermModel.rank_integral_selfDual E H D 1 _ G φ hξ hm
  obtain ⟨hinj, hspan, hG, hdet, hEF⟩ := hm
  rw [Matrix.det_fin_one] at hdet
  have hherm : ∀ x y, FD.herm G x y = G 0 0 * x 0 * IsCMField.complexConj E (y 0) := fun x y => by
    simp only [FD.herm, FD.cc, Fin.sum_univ_one]; ring
  simp only [hherm] at hdual hEF
  have hβ : IsCMField.complexConj E (G 0 0) = G 0 0 := hG 0 0
  generalize G 0 0 = β at hdet hdual hEF hβ
  let e : D.La →ₗ[𝓞 E] E := LinearMap.proj 0 ∘ₗ φ
  have he : ∀ x, φ x 0 = e x := fun _ => rfl
  simp only [he] at hdual hEF
  have heinj : Function.Injective e := fun x y hxy => hinj (funext fun i => by rw [Subsingleton.elim i 0]; exact hxy)
  have hfg' : (LinearMap.range e).FG := by
    rw [LinearMap.range_comp]; exact hfg.map _
  let 𝔞 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E := ⟨_, FractionalIdeal.isFractional_of_fg hfg'⟩
  have hmem : ∀ v, v ∈ 𝔞 ↔ ∃ x, e x = v := fun v => Iff.rfl
  have : Nontrivial D.La := Module.nontrivial_of_finrank_pos (R := 𝓞 E) (by rw [D.rank, hr]; exact one_pos)
  obtain ⟨a, ha⟩ := exists_ne (0 : D.La)
  have ha' : e a ≠ 0 := (map_ne_zero_iff _ heinj).2 ha
  have h𝔞 : 𝔞 ≠ 0 := fun h0 => ha' (FractionalIdeal.eq_zero_iff.1 h0 _ ((hmem _).2 ⟨a, rfl⟩))
  have hsm : ∀ (s : 𝓞 E) x, e (s • x) = s * e x := fun s x => by rw [map_smul]; rfl
  have hE : ∀ x y, (((ε : ℤ) * D.EF x y : ℤ) : ℚ) =
      Algebra.trace ℚ E (β * e x * IsCMField.complexConj E (e y) / H.rt) := fun x y => by
    rw [Int.cast_mul, hEF, ← zsmul_eq_mul, ← map_zsmul, zsmul_eq_mul, ← _root_.mul_assoc, ← mul_div_assoc, hε]
    congr 1; ring
  have hE' : ∀ x y, (((ε : ℤ) * D.EF (H.w0 • x) y : ℤ) : ℚ) =
      Algebra.trace ℚ E (H.w0 * (β * e x * IsCMField.complexConj E (e y)) / H.rt) := fun x y => by
    rw [hE, hsm]; congr 1; ring
  refine ⟨𝔞, e, β, h𝔞, heinj, rfl, hβ, re_pos_of_trace_pos hβ hdet fun v hv => ?_, fun Ω _ _ hΩ τ₀ x y => ?_, ?_⟩
  · obtain ⟨s, n, hn, hs⟩ : ∃ (s : 𝓞 E) (n : ℤ), n ≠ 0 ∧ (s : E) = n * (v / e a) := by
      obtain ⟨n, hn, hi⟩ := ((IsFractionRing.isAlgebraic_iff ℤ ℚ E).2
        (Algebra.IsAlgebraic.isAlgebraic (v / e a))).exists_integral_multiple
      exact ⟨⟨_, hi⟩, n, hn, zsmul_eq_mul _ _⟩
    have hx : e (s • a) = n * v := by rw [hsm, hs]; field_simp
    have h1 : (0 : ℚ) < (((ε : ℤ) * D.EF (H.w0 • s • a) (s • a) : ℤ) : ℚ) := by
      exact_mod_cast hpos _ ((map_ne_zero_iff _ heinj).1 (hx ▸ mul_ne_zero (Int.cast_ne_zero.2 hn) hv))
    have h2 := hE (s • a) (s • a)
    rw [D.alt, mul_zero, Int.cast_zero] at h2
    rw [hE'] at h1
    have h3 : (H.w0 : E) * (β * e (s • a) * IsCMField.complexConj E (e (s • a))) / H.rt =
        (2⁻¹ : ℚ) • (β * e (s • a) * IsCMField.complexConj E (e (s • a)) / H.rt) +
          ((n : ℚ) ^ 2 / 2) • (β * v * IsCMField.complexConj E v) := by
      rw [hx, map_mul, map_intCast, Rat.smul_def, Rat.smul_def]
      push_cast
      field_simp
      rw [coe_rt_eq]
      ring
    rw [h3, map_add, map_smul (Algebra.trace ℚ E), map_smul (Algebra.trace ℚ E), ← h2, smul_zero, zero_add,
      smul_eq_mul] at h1
    exact (mul_pos_iff_of_pos_left (by positivity)).1 h1
  · rw [← relTrace_eq H hΩ, ← hE, ← hE', hh]
    push_cast
    simp only [map_add, map_mul, map_sub, map_intCast]
    ring
  · have h1 := log_absNorm_of_selfDual h𝔞 (mul_ne_zero (div_ne_zero hε0 hrt) hdet) fun v => by
      have h2 := hdual fun _ => v
      simp only [← _root_.mul_assoc] at h2
      constructor
      · intro hv y hy
        obtain ⟨x, rfl⟩ := (hmem _).1 hv
        obtain ⟨y, rfl⟩ := (hmem _).1 hy
        exact h2.2 ⟨x, funext fun i => by rw [Subsingleton.elim i 0]; rfl⟩ y
      · intro hv
        obtain ⟨x, hx⟩ := h2.1 fun y => hv _ ((hmem _).2 ⟨y, rfl⟩)
        exact (hmem _).2 ⟨x, congrFun hx 0⟩
    have h2 : Real.log |(Algebra.norm ℚ (((ε : ℤ) : E) / H.rt * β) : ℚ)| =
        Real.log |(Algebra.norm ℚ β : ℚ)| - Real.log |(Algebra.norm ℚ (H.rt : E) : ℚ)| := by
      have n1 : (Algebra.norm ℚ β : ℝ) ≠ 0 := by exact_mod_cast Algebra.norm_ne_zero_iff.2 hdet
      have n2 : (Algebra.norm ℚ (H.rt : E) : ℝ) ≠ 0 := by exact_mod_cast Algebra.norm_ne_zero_iff.2 hrt
      have n3 : |(Algebra.norm ℚ ((ε : ℤ) : E) : ℝ)| = 1 := by
        rw [← map_intCast (algebraMap ℚ E), Algebra.norm_algebraMap]
        rcases Int.units_eq_one_or ε with rfl | rfl <;> simp
      rw [div_eq_mul_inv, map_mul, map_mul, Algebra.norm_inv]
      push_cast
      rw [abs_mul, abs_mul, n3, _root_.one_mul, Real.log_mul (by simpa using n2) (by simpa using n1), abs_inv, Real.log_inv]
      ring
    rw [h2, log_norm_rt] at h1
    linear_combination h1

end GlobalTheory.CM
end
