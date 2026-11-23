import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.CmLatticeCommutatorPairingPowEqOneOfGoodLift
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ConstantCoeffShiftS

noncomputable section
open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology

namespace GlobalTheory.MomOne.TwistMom
open GlobalTheory.MomOne.Shift
variable {q : ℕ} [Fact q.Prime]

theorem norm_zc (a : ℤ_[q]) : ‖zc a‖ = ‖a‖ := by
  have h := PadicComplex.norm_extends' q (a : ℚ_[q])
  simpa [zc] using h

theorem zc_natCast (m : ℕ) : zc (m : ℤ_[q]) = (m : ℂ_[q]) := by simp [zc]

theorem continuous_zc : Continuous (zc : ℤ_[q] → ℂ_[q]) := by
  refine (Isometry.of_dist_eq fun a b => ?_).continuous
  rw [dist_eq_norm, dist_eq_norm, ← norm_zc]
  simp [zc]

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

theorem continuous_redFun (r : ℕ) (g : ZMod (q ^ r) → ℂ_[q]) :
    Continuous fun a : ℤ_[q] => g (PadicInt.toZModPow r a) := by
  have hl : q.Prime := Fact.out
  rw [continuous_iff_continuousAt]
  intro x
  refine (continuousAt_const (y := g (PadicInt.toZModPow r x))).congr ?_
  have hpos : (0 : ℝ) < (q : ℝ) ^ (-(r : ℤ)) := zpow_pos (by exact_mod_cast hl.pos) _
  filter_upwards [Metric.closedBall_mem_nhds x hpos] with y hy
  rw [Metric.mem_closedBall, dist_eq_norm, PadicInt.norm_le_pow_iff_mem_span_pow,
    ← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, sub_eq_zero] at hy
  rw [hy]

theorem hasSum_coeff_iter {ζ : ℂ_[q]} (h : ‖ζ - 1‖ < 1) {S : ℂ_[q]⟦X⟧} (hS : Bdd S) (k : ℕ) :
    ∀ n, HasSum (fun m => coeff m S * coeff n (DT^[k] (sS ζ ^ m)))
      (coeff n (DT^[k] (shiftS ζ S))) := by
  obtain ⟨B, hB⟩ := hS
  induction k with
  | zero =>
    intro n
    simp only [Function.iterate_zero, id]
    rw [coeff_shiftS]
    exact (summable_term h hB n).hasSum
  | succ k ih =>
    intro n
    simp only [Function.iterate_succ_apply', coeff_DT]
    have := ((ih (n + 1)).mul_right ((n : ℂ_[q]) + 1)).add ((ih n).mul_right (n : ℂ_[q]))
    simpa only [mul_add, mul_assoc] using this

theorem DT_one_add_pow (c : ℂ_[q]) (j : ℕ) :
    DT (C c * (1 + X) ^ j) = C (c * j) * (1 + X) ^ j := by
  cases j with
  | zero => simp [DT]
  | succ j =>
    have hd : derivative ℂ_[q] (1 + X : ℂ_[q]⟦X⟧) = 1 := by
      rw [map_add, derivative_X, Derivation.map_one_eq_zero, zero_add]
    rw [DT, ← smul_eq_C_mul, Derivation.map_smul, Derivation.leibniz_pow, hd, smul_eq_C_mul,
      map_mul, map_natCast]
    simp only [Nat.add_sub_cancel, smul_eq_mul, nsmul_eq_mul]
    ring

theorem DT_iter_sum (s : Finset ℕ) (c : ℕ → ℂ_[q]) (k : ℕ) :
    DT^[k] (∑ j ∈ s, C (c j) * (1 + X) ^ j) = ∑ j ∈ s, C (c j * (j : ℂ_[q]) ^ k) * (1 + X) ^ j := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, DT, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    have := DT_one_add_pow (c j * (j : ℂ_[q]) ^ k) j
    rw [DT] at this
    rw [this, pow_succ, mul_assoc]

theorem sS_pow_eq (ζ : ℂ_[q]) (m : ℕ) :
    sS ζ ^ m = ∑ j ∈ Finset.range (m + 1),
      C ((-1) ^ (m - j) * (m.choose j : ℂ_[q]) * ζ ^ j) * (1 + X) ^ j := by
  rw [sS, sub_eq_add_neg, add_pow]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [map_mul, map_pow, map_neg, map_one, map_natCast, mul_pow]
  ring

theorem twisted_moments : ∀ (q : ℕ) [Fact q.Prime] (S : ℂ_[q]⟦X⟧) (ζ : ℂ_[q]) (n k : ℕ), Bdd S → ζ ^ (q ^ n) = 1 → ∃ f : C(ℤ_[q], ℂ_[q]), (∀ a, f a = ζ ^ (PadicInt.toZModPow n a).val * zc a ^ k) ∧ HasSum (fun m : ℕ => coeff m S * (fwdDiff (1 : ℤ_[q]))^[m] f 0) (constantCoeff (DT^[k] (shiftS ζ S))) := by
  intro q _ S ζ n k hS h
  have hζ := norm_sub_one_lt_of_root h
  refine ⟨⟨fun a => ζ ^ (PadicInt.toZModPow n a).val * zc a ^ k,
    (continuous_redFun n fun x => ζ ^ x.val).mul (continuous_zc.pow k)⟩, fun _ => rfl, ?_⟩
  have := hasSum_coeff_iter hζ hS k 0
  rw [coeff_zero_eq_constantCoeff] at this
  convert this using 3 with m
  rw [fwdDiff_iter_eq_sum_shift, sS_pow_eq, DT_iter_sum, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have e : (0 : ℤ_[q]) + j • (1 : ℤ_[q]) = (j : ℤ_[q]) := by simp
  rw [e]
  simp only [ContinuousMap.coe_mk, map_natCast, ZMod.val_natCast, zc_natCast]
  rw [← pow_eq_pow_mod j h]
  simp
  ring

end GlobalTheory.MomOne.TwistMom
