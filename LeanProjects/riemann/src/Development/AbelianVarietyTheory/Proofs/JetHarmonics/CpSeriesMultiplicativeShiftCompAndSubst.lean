import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.CmLatticeCommutatorPairingPowEqOneOfGoodLift
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CpSeriesCoeffNormBoundedRingLaws
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ConstantCoeffShiftS

noncomputable section
open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology

namespace GlobalTheory.MomOne.ShiftComp
variable {q : ℕ} [Fact q.Prime]

theorem bd_nonneg {B : ℝ} {f : ℂ_[q]⟦X⟧} (h : Bd B f) : 0 ≤ B := (norm_nonneg _).trans (h 0)

theorem coeff_pow_mul_le (u h : ℂ_[q]⟦X⟧) (B : ℝ) (hu : Bd 1 u) (hh : Bd B h) (N : ℕ) :
    ∀ n, ‖coeff n (u ^ N * h)‖ ≤ B * ‖coeff 0 u‖ ^ (N - n) := by
  have hB := bd_nonneg hh
  have hr0 : 0 ≤ ‖coeff 0 u‖ := norm_nonneg _
  have hr1 : ‖coeff 0 u‖ ≤ 1 := hu 0
  induction N with
  | zero => intro n; simpa using hh n
  | succ N ih =>
    intro n
    rw [pow_succ', mul_assoc, coeff_mul]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun x hx => ?_
    have hx' : x.1 + x.2 = n := by simpa using hx
    rw [norm_mul]
    rcases Nat.eq_zero_or_pos x.1 with h0 | h0
    · rw [h0]
      calc _ ≤ ‖coeff 0 u‖ * (B * ‖coeff 0 u‖ ^ (N - x.2)) := mul_le_mul_of_nonneg_left (ih _) hr0
        _ = B * ‖coeff 0 u‖ ^ (N - x.2 + 1) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hr0 hr1 (by omega)) hB
    · calc _ ≤ 1 * (B * ‖coeff 0 u‖ ^ (N - x.2)) :=
            mul_le_mul (hu _) (ih _) (norm_nonneg _) zero_le_one
        _ = B * ‖coeff 0 u‖ ^ (N - x.2) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hr0 hr1 (by omega)) hB

structure Hom (Φ : ℂ_[q]⟦X⟧ → ℂ_[q]⟦X⟧) : Prop where
  bd : ∀ f B, Bd B f → Bd B (Φ f)
  add : ∀ f g, Bdd f → Bdd g → Φ (f + g) = Φ f + Φ g
  mul : ∀ f g, Bdd f → Bdd g → Φ (f * g) = Φ f * Φ g
  const : ∀ c, Φ (C c) = C c

theorem hom_shift {ζ : ℂ_[q]} (hζ : ‖ζ - 1‖ < 1) : Hom (shiftS ζ) where
  bd := (GlobalTheory.MomOne.Shift.shift_laws q ζ hζ).1
  add f g hf hg := ((GlobalTheory.MomOne.Shift.shift_laws q ζ hζ).2.1 f g hf hg).1
  mul f g hf hg := ((GlobalTheory.MomOne.Shift.shift_laws q ζ hζ).2.1 f g hf hg).2
  const := (GlobalTheory.MomOne.Shift.shift_laws q ζ hζ).2.2.1

theorem bd_X : Bd 1 (X : ℂ_[q]⟦X⟧) := by
  intro n; rw [coeff_X]; split_ifs <;> simp

theorem bdd_C (c : ℂ_[q]) : Bdd (C c : ℂ_[q]⟦X⟧) := by
  refine ⟨‖c‖, fun n => ?_⟩
  rw [coeff_C]; split_ifs <;> simp

theorem bdd_add {f g : ℂ_[q]⟦X⟧} (hf : Bdd f) (hg : Bdd g) : Bdd (f + g) := by
  obtain ⟨A, hA⟩ := hf
  obtain ⟨B, hB⟩ := hg
  exact ⟨A + B, fun n => by rw [map_add]; exact (norm_add_le _ _).trans (add_le_add (hA n) (hB n))⟩

theorem bdd_mul {f g : ℂ_[q]⟦X⟧} (hf : Bdd f) (hg : Bdd g) : Bdd (f * g) := by
  obtain ⟨A, hA⟩ := hf
  obtain ⟨B, hB⟩ := hg
  refine ⟨A * B, fun n => ?_⟩
  rw [coeff_mul]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg
    (mul_nonneg (bd_nonneg hA) (bd_nonneg hB)) fun x _ => ?_
  rw [norm_mul]
  exact mul_le_mul (hA _) (hB _) (norm_nonneg _) (bd_nonneg hA)

theorem Hom.comp {Φ Ψ : ℂ_[q]⟦X⟧ → ℂ_[q]⟦X⟧} (h : Hom Φ) (h' : Hom Ψ) : Hom (fun f => Φ (Ψ f)) where
  bd f B hf := h.bd _ _ (h'.bd _ _ hf)
  add f g hf hg := by
    rw [h'.add f g hf hg, h.add _ _ (hf.imp fun B hB => h'.bd _ _ hB) (hg.imp fun B hB => h'.bd _ _ hB)]
  mul f g hf hg := by
    rw [h'.mul f g hf hg, h.mul _ _ (hf.imp fun B hB => h'.bd _ _ hB) (hg.imp fun B hB => h'.bd _ _ hB)]
  const c := by rw [h'.const, h.const]

theorem Hom.ext {Φ Ψ : ℂ_[q]⟦X⟧ → ℂ_[q]⟦X⟧} (h : Hom Φ) (h' : Hom Ψ) (hX : Φ X = Ψ X)
    (h0 : ‖coeff 0 (Ψ X)‖ < 1) (f : ℂ_[q]⟦X⟧) (hf : Bdd f) : Φ f = Ψ f := by
  obtain ⟨B, hB⟩ := hf
  have key : ∀ N : ℕ, ∀ f, Bd B f → ∃ g, Bd (B + B) g ∧ Φ f - Ψ f = Ψ X ^ N * g := by
    intro N
    induction N with
    | zero =>
      intro f hf
      refine ⟨Φ f - Ψ f, fun n => ?_, by simp⟩
      rw [map_sub]
      exact (norm_sub_le _ _).trans (add_le_add (h.bd _ _ hf n) (h'.bd _ _ hf n))
    | succ N ih =>
      intro f hf
      have hg : Bd B (PowerSeries.mk fun p => coeff (p + 1) f) := fun n => by
        rw [coeff_mk]; exact hf _
      obtain ⟨g, hg1, hg2⟩ := ih _ hg
      refine ⟨g, hg1, ?_⟩
      have e := eq_X_mul_shift_add_const f
      have b1 : Bdd (X : ℂ_[q]⟦X⟧) := ⟨1, bd_X⟩
      rw [e, h.add _ _ (bdd_mul b1 ⟨B, hg⟩) (bdd_C _), h'.add _ _ (bdd_mul b1 ⟨B, hg⟩) (bdd_C _),
        h.mul _ _ b1 ⟨B, hg⟩, h'.mul _ _ b1 ⟨B, hg⟩, h.const, h'.const, hX, pow_succ', mul_assoc, ← hg2]
      ring
  rw [← sub_eq_zero]
  ext n
  rw [map_zero, ← norm_le_zero_iff]
  have lim : Filter.Tendsto (fun N : ℕ => (B + B) * ‖coeff 0 (Ψ X)‖ ^ N) Filter.atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) h0).const_mul (B + B)
  refine ge_of_tendsto' lim fun N => ?_
  obtain ⟨g, hg1, hg2⟩ := key (N + n) f hB
  rw [hg2]
  simpa using coeff_pow_mul_le _ g _ (h'.bd _ _ bd_X) hg1 (N + n) n

theorem shift_X {ζ : ℂ_[q]} (hζ : ‖ζ - 1‖ < 1) : shiftS ζ X = C ζ * (1 + X) - 1 :=
  (GlobalTheory.MomOne.Shift.shift_laws q ζ hζ).2.2.2.1

theorem Hom.lin {Φ : ℂ_[q]⟦X⟧ → ℂ_[q]⟦X⟧} (h : Hom Φ) (c : ℂ_[q]) :
    Φ (C c * (1 + X) - 1) = C c * (1 + Φ X) - 1 := by
  have b1 : Bdd (X : ℂ_[q]⟦X⟧) := ⟨1, bd_X⟩
  have e : (C c * (1 + X) - 1 : ℂ_[q]⟦X⟧) = C c * X + C (c - 1) := by rw [map_sub, map_one]; ring
  rw [e, h.add _ _ (bdd_mul (bdd_C _) b1) (bdd_C _), h.mul _ _ (bdd_C _) b1, h.const, h.const, map_sub, map_one]
  ring

theorem norm_le_one_of {ζ : ℂ_[q]} (hζ : ‖ζ - 1‖ < 1) : ‖ζ‖ ≤ 1 := by
  have := IsUltrametricDist.norm_add_le_max (ζ - 1) 1
  rw [sub_add_cancel, norm_one] at this
  exact this.trans (max_le hζ.le le_rfl)

theorem norm_mul_sub_one {ζ ξ : ℂ_[q]} (hζ : ‖ζ - 1‖ < 1) (hξ : ‖ξ - 1‖ < 1) : ‖ζ * ξ - 1‖ < 1 := by
  have e : ζ * ξ - 1 = ζ * (ξ - 1) + (ζ - 1) := by ring
  rw [e]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ?_ hζ)
  rw [norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _) (norm_le_one_of hζ)).trans_lt hξ

theorem norm_pow_sub_one {ζ : ℂ_[q]} (hζ : ‖ζ - 1‖ < 1) (k : ℕ) : ‖ζ ^ k - 1‖ < 1 := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ]; exact norm_mul_sub_one ih hζ

theorem shift_shift (ζ ξ : ℂ_[q]) (f : ℂ_[q]⟦X⟧) (hζ : ‖ζ - 1‖ < 1) (hξ : ‖ξ - 1‖ < 1) (hf : Bdd f) :
    shiftS ζ (shiftS ξ f) = shiftS (ζ * ξ) f := by
  have hm := norm_mul_sub_one hζ hξ
  refine ((hom_shift hζ).comp (hom_shift hξ)).ext (hom_shift hm) ?_ ?_ f hf
  · show shiftS ζ (shiftS ξ X) = _
    rw [shift_X hξ, (hom_shift hζ).lin, shift_X hζ, shift_X hm, map_mul]
    ring
  · rw [shift_X hm]
    simpa using hm

theorem norm_zc (a : ℤ_[q]) : ‖zc a‖ = ‖a‖ := by
  have h := PadicComplex.norm_extends' q (a : ℚ_[q])
  simpa [zc] using h

theorem zc_natCast (m : ℕ) : zc (m : ℤ_[q]) = (m : ℂ_[q]) := by simp [zc]

theorem continuous_zc : Continuous (zc : ℤ_[q] → ℂ_[q]) := by
  refine (Isometry.of_dist_eq fun a b => ?_).continuous
  rw [dist_eq_norm, dist_eq_norm, ← norm_zc]
  simp [zc]

theorem bd_mulS (a : ℤ_[q]) : Bd 1 (mulS a) := by
  intro n
  rw [mulS, coeff_mk]
  split_ifs
  · simp
  · rw [norm_zc]; exact PadicInt.norm_le_one _

theorem const_mulS (a : ℤ_[q]) : constantCoeff (mulS a) = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply, mulS, coeff_mk]; simp

theorem continuous_coeff_mulS (n : ℕ) : Continuous fun a : ℤ_[q] => coeff n (mulS a) := by
  simp only [mulS, coeff_mk]
  split_ifs
  · exact continuous_const
  · exact continuous_zc.comp (PadicInt.continuous_choose n)

theorem mulS_natCast (m : ℕ) : mulS (m : ℤ_[q]) = (1 + X) ^ m - 1 := by
  ext n
  have e : ((1 + X : ℂ_[q]⟦X⟧)) ^ m = (((1 + Polynomial.X) ^ m : Polynomial ℂ_[q]) : ℂ_[q]⟦X⟧) := by simp
  rw [mulS, coeff_mk, map_sub, e, Polynomial.coeff_coe, Polynomial.coeff_one_add_X_pow, coeff_one,
    Ring.choose_natCast, zc_natCast]
  split_ifs with h
  · simp [h]
  · simp

theorem hom_subst (a : ℤ_[q]) : Hom (fun f : ℂ_[q]⟦X⟧ => f.subst (mulS a : ℂ_[q]⟦X⟧)) where
  bd f B hf := (GlobalTheory.MomOne.sup_norm_laws q).2.1 f _ B hf (bd_mulS a) (const_mulS a)
  add f g _ _ := subst_add (HasSubst.of_constantCoeff_zero' (const_mulS a)) f g
  mul f g _ _ := subst_mul (HasSubst.of_constantCoeff_zero' (const_mulS a)) f g
  const c := subst_C c

theorem shift_mulS_natCast {ζ : ℂ_[q]} (hζ : ‖ζ - 1‖ < 1) (m : ℕ) :
    shiftS ζ (mulS (m : ℤ_[q])) = C (ζ ^ m) * (1 + mulS (m : ℤ_[q])) - 1 := by
  have h := hom_shift hζ
  have b1 : Bdd (1 + X : ℂ_[q]⟦X⟧) := bdd_add (by simpa using bdd_C (1 : ℂ_[q])) ⟨1, bd_X⟩
  have h1 : shiftS ζ (1 + X) = C ζ * (1 + X) := by
    rw [show (1 + X : ℂ_[q]⟦X⟧) = C 1 + X by simp, h.add _ _ (bdd_C _) ⟨1, bd_X⟩, h.const, shift_X hζ, map_one]
    ring
  have hp : ∀ m : ℕ, Bdd ((1 + X : ℂ_[q]⟦X⟧) ^ m) ∧ shiftS ζ ((1 + X) ^ m) = C (ζ ^ m) * (1 + X) ^ m := by
    intro m
    induction m with
    | zero => exact ⟨by simpa using bdd_C (1 : ℂ_[q]), by simpa using h.const 1⟩
    | succ m ih =>
      refine ⟨by rw [pow_succ]; exact bdd_mul ih.1 b1, ?_⟩
      rw [pow_succ, h.mul _ _ ih.1 b1, ih.2, h1, map_pow, map_pow]
      ring
  rw [mulS_natCast, show ((1 + X) ^ m - 1 : ℂ_[q]⟦X⟧) = (1 + X) ^ m + C (-1) by simp [sub_eq_add_neg],
    h.add _ _ (hp m).1 (bdd_C _), h.const, (hp m).2]
  simp [sub_eq_add_neg]

theorem continuous_coeff_shift_mulS {ζ : ℂ_[q]} (hζ : ‖ζ - 1‖ < 1) (n : ℕ) :
    Continuous fun a : ℤ_[q] => coeff n (shiftS ζ (mulS a)) := by
  simp only [shiftS, coeff_mk]
  refine continuous_tsum (u := fun m => ‖ζ - 1‖ ^ (m - n))
    (fun m => (continuous_coeff_mulS m).mul continuous_const) ?_ fun m a => ?_
  · rw [← summable_nat_add_iff n]
    simpa using summable_geometric_of_lt_one (norm_nonneg _) hζ
  · rw [norm_mul, norm_mul, norm_mul, norm_pow, norm_pow]
    have h1 := bd_mulS a m
    have h2 : ‖(m.choose n : ℂ_[q])‖ ≤ 1 := IsUltrametricDist.norm_natCast_le_one _ _
    have h3 : ‖ζ‖ ^ n ≤ 1 := pow_le_one₀ (norm_nonneg _) (norm_le_one_of hζ)
    calc _ ≤ 1 * (1 * 1 * ‖ζ - 1‖ ^ (m - n)) := by gcongr
      _ = _ := by ring

theorem norm_sub_one_lt_of_root {ζ : ℂ_[q]} {n : ℕ} (h : ζ ^ (q ^ n) = 1) : ‖ζ - 1‖ < 1 := by
  have hp : q.Prime := Fact.out
  have hn : q ^ n ≠ 0 := pow_ne_zero _ hp.ne_zero
  have h1 : ‖ζ‖ = 1 := by
    have := congrArg norm h
    rw [norm_pow, norm_one] at this
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn).mp this
  let O : Subring ℂ_[q] :=
    { carrier := {x | ‖x‖ ≤ 1}
      mul_mem' := fun {a b} ha hb => by
        show ‖a * b‖ ≤ 1
        rw [norm_mul]; exact mul_le_one₀ ha (norm_nonneg _) hb
      one_mem' := by simp
      add_mem' := fun {a b} ha hb => (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb)
      zero_mem' := by simp
      neg_mem' := fun {a} ha => by simpa using ha }
  have hz : ζ ∈ O := h1.le
  obtain ⟨r, hr⟩ := exists_add_pow_prime_pow_eq hp ((⟨ζ, hz⟩ : O) - 1) 1 n
  have hr' := congrArg (fun x : O => (x : ℂ_[q])) hr
  simp only [sub_add_cancel] at hr'
  push_cast at hr'
  have hq : ‖(q : ℂ_[q])‖ < 1 := by
    rw [← zc_natCast, norm_zc]; exact Padic.norm_p_lt_one
  have e : (ζ - 1) ^ q ^ n = -((q : ℂ_[q]) * ((ζ - 1) * r)) := by
    rw [h, one_pow] at hr'
    linear_combination -hr'
  have hm : ‖(ζ - 1) * r‖ ≤ 1 := O.mul_mem (O.sub_mem hz O.one_mem) r.2
  have : ‖ζ - 1‖ ^ q ^ n < 1 := by
    rw [← norm_pow, e, norm_neg, norm_mul]
    exact (mul_le_of_le_one_right (norm_nonneg _) hm).trans_lt hq
  exact (pow_lt_one_iff_of_nonneg (norm_nonneg _) hn).mp this

theorem shift_mulS {ζ : ℂ_[q]} {n k : ℕ} {a : ℤ_[q]} (h : ζ ^ (q ^ n) = 1)
    (ha : ‖a - (k : ℤ_[q])‖ ≤ (q : ℝ) ^ (-(n : ℤ))) :
    shiftS ζ (mulS a) = C (ζ ^ k) * (1 + mulS a) - 1 := by
  have hζ := norm_sub_one_lt_of_root h
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.mp ((PadicInt.norm_le_pow_iff_mem_span_pow _ _).mp ha)
  obtain rfl : a = k + b * (q : ℤ_[q]) ^ n := by rw [hb]; ring
  clear hb ha
  ext j
  have hc : Continuous fun b : ℤ_[q] => (k : ℤ_[q]) + b * (q : ℤ_[q]) ^ n := by fun_prop
  refine PadicInt.denseRange_natCast.induction_on b (isClosed_eq ?_ ?_) fun m => ?_
  · exact (continuous_coeff_shift_mulS hζ j).comp hc
  · simp only [map_sub, coeff_C_mul, map_add]
    exact (continuous_const.mul (continuous_const.add ((continuous_coeff_mulS j).comp hc))).sub continuous_const
  · have e : (k : ℤ_[q]) + (m : ℤ_[q]) * (q : ℤ_[q]) ^ n = ((k + q ^ n * m : ℕ) : ℤ_[q]) := by
      push_cast; ring
    rw [e, shift_mulS_natCast hζ, pow_add, pow_mul, h, one_pow, mul_one]

theorem shift_subst (ζ : ℂ_[q]) (n k : ℕ) (a : ℤ_[q]) (f : ℂ_[q]⟦X⟧) (h : ζ ^ (q ^ n) = 1)
    (ha : ‖a - (k : ℤ_[q])‖ ≤ (q : ℝ) ^ (-(n : ℤ))) (hf : Bdd f) :
    shiftS ζ (f.subst (mulS a : ℂ_[q]⟦X⟧)) = (shiftS (ζ ^ k) f).subst (mulS a : ℂ_[q]⟦X⟧) := by
  have hζ := norm_sub_one_lt_of_root h
  have hk := norm_pow_sub_one hζ k
  have hX : (X : ℂ_[q]⟦X⟧).subst (mulS a : ℂ_[q]⟦X⟧) = mulS a :=
    subst_X (HasSubst.of_constantCoeff_zero' (const_mulS a))
  have e : (shiftS (ζ ^ k) X).subst (mulS a : ℂ_[q]⟦X⟧) = C (ζ ^ k) * (1 + mulS a) - 1 := by
    rw [shift_X hk]
    have := (hom_subst a).lin (ζ ^ k)
    rw [hX] at this
    exact this
  refine ((hom_shift hζ).comp (hom_subst a)).ext ((hom_subst a).comp (hom_shift hk)) ?_ ?_ f hf
  · show shiftS ζ ((X : ℂ_[q]⟦X⟧).subst (mulS a : ℂ_[q]⟦X⟧)) = (shiftS (ζ ^ k) X).subst (mulS a : ℂ_[q]⟦X⟧)
    rw [hX, e, shift_mulS h ha]
  · show ‖coeff 0 ((shiftS (ζ ^ k) X).subst (mulS a : ℂ_[q]⟦X⟧))‖ < 1
    rw [e]
    simpa [const_mulS] using hk

theorem main : ∀ (q : ℕ) [Fact q.Prime], (∀ (ζ ξ : ℂ_[q]) (f : ℂ_[q]⟦X⟧), ‖ζ - 1‖ < 1 → ‖ξ - 1‖ < 1 → Bdd f → shiftS ζ (shiftS ξ f) = shiftS (ζ * ξ) f) ∧ ∀ (ζ : ℂ_[q]) (n k : ℕ) (a : ℤ_[q]) (f : ℂ_[q]⟦X⟧), ζ ^ (q ^ n) = 1 → ‖a - (k : ℤ_[q])‖ ≤ (q : ℝ) ^ (-(n : ℤ)) → Bdd f → ‖ζ - 1‖ < 1 ∧ shiftS ζ (f.subst (mulS a : ℂ_[q]⟦X⟧)) = (shiftS (ζ ^ k) f).subst (mulS a : ℂ_[q]⟦X⟧) :=
  fun _ _ => ⟨shift_shift, fun ζ n k a f h ha hf => ⟨norm_sub_one_lt_of_root h, shift_subst ζ n k a f h ha hf⟩⟩

end GlobalTheory.MomOne.ShiftComp
