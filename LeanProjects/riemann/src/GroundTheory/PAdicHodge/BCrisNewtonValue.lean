import Mathlib
import GroundTheory.PAdicHodge.BCrisNewtonSlope
import GroundTheory.PAdicHodge.BCrisNewtonDom
import GroundTheory.PAdicHodge.BCrisPlusInvariants
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

namespace ACris

open _root_.WittVector Laurent Polynomial WittTilt

variable {p : ℕ} [hp : Fact p.Prime]

local notation "𝔸" => Localization.Away (p : AInf ℂ_[p] p)
local notation "𝔹" => BDeRhamPlus (normInteger ℂ_[p]) p

variable (p) in

def sig (ρ : ℝ) : ℝ := Real.log ρ / Real.log (p : ℝ)⁻¹

theorem inv_p_pos : (0 : ℝ) < (p : ℝ)⁻¹ := inv_pos.2 (Nat.cast_pos.2 hp.out.pos)

theorem inv_p_lt_one : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (Nat.one_lt_cast.2 hp.out.one_lt)

theorem log_inv_p_neg : Real.log (p : ℝ)⁻¹ < 0 := Real.log_neg inv_p_pos inv_p_lt_one

theorem rpow_sig {ρ : ℝ} (hρ : 0 < ρ) : ((p : ℝ)⁻¹) ^ sig p ρ = ρ := by
  rw [Real.rpow_def_of_pos inv_p_pos]
  have : Real.log (p : ℝ)⁻¹ * sig p ρ = Real.log ρ := by
    unfold sig
    rw [← mul_div_assoc]
    exact mul_div_cancel_left₀ _ log_inv_p_neg.ne
  rw [this, Real.exp_log hρ]

theorem sig_pos {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) : 0 < sig p ρ :=
  div_pos_of_neg_of_neg (Real.log_neg hρ0 hρ1) log_inv_p_neg

theorem sig_inv_p : sig p (p : ℝ)⁻¹ = 1 := div_self log_inv_p_neg.ne

theorem norm_p_Cp : ‖(p : ℂ_[p])‖ = (p : ℝ)⁻¹ := by
  rw [← PadicComplex.coe_natCast, PadicComplex.norm_extends,
    ← map_natCast (algebraMap ℚ_[p] (PadicAlgCl p)) p, PadicAlgCl.norm_extends, Padic.norm_p]

theorem norm_p_algCl : ‖(p : PadicAlgCl p)‖ = (p : ℝ)⁻¹ := by
  rw [← map_natCast (algebraMap ℚ_[p] (PadicAlgCl p)) p, PadicAlgCl.norm_extends, Padic.norm_p]

theorem pow_rpow_comm {x : ℝ} (hx : 0 ≤ x) (n : ℕ) (s : ℝ) : (x ^ n) ^ s = (x ^ s) ^ n := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx, mul_comm, Real.rpow_mul hx, Real.rpow_natCast]

theorem gn_padicInt {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (c : ℤ_[p]) :
    gn ℂ_[p] p ρ (algebraMap (AInf ℂ_[p] p) 𝔸 (IsPerfectoidField.padicIntToWitt (K := ℂ_[p]) p c)) =
      ‖c‖ ^ sig p ρ := by
  by_cases hc : c = 0
  · subst hc
    rw [map_zero, map_zero, gn_zero, norm_zero, Real.zero_rpow (sig_pos hρ0 hρ1).ne']
  · have hn : ‖c‖ = ((p : ℝ)⁻¹) ^ c.valuation := by
      conv_lhs => rw [PadicInt.unitCoeff_spec hc]
      rw [norm_mul, PadicInt.norm_units, one_mul, norm_pow, PadicInt.norm_p]
    conv_lhs => rw [PadicInt.unitCoeff_spec hc]
    rw [map_mul, map_mul, map_pow, map_pow, map_natCast, map_natCast, gn_mul hρ0 hρ1,
      gn_unit hρ0 hρ1 ((PadicInt.unitCoeff hc).isUnit.map _), one_mul, gn_pow hρ0 hρ1,
      gn_natCast_p hρ0, hn, pow_rpow_comm inv_p_pos.le, rpow_sig hρ0]

theorem natDegree_minpoly_pos (y : PadicAlgCl p) : 0 < (minpoly ℚ_[p] y).natDegree :=
  minpoly.natDegree_pos (Algebra.IsIntegral.isIntegral y)

theorem norm_minpoly_coeff_le (y : PadicAlgCl p) {i : ℕ} (hi : i ≤ (minpoly ℚ_[p] y).natDegree) :
    ‖(minpoly ℚ_[p] y).coeff i‖ ≤ ‖y‖ ^ ((minpoly ℚ_[p] y).natDegree - i) := by
  set q := minpoly ℚ_[p] y with hq
  rcases hi.lt_or_eq with hi | hi
  · have h1 : ‖q.coeff i‖ ^ (1 / (q.natDegree - i : ℝ)) ≤ ‖y‖ := by
      have e : ‖y‖ = spectralValue q := rfl
      rw [e, ← spectralValueTerms_of_lt_natDegree _ hi]
      exact le_ciSup (spectralValueTerms_bddAbove _) i
    have hpos : (0 : ℝ) < (q.natDegree - i : ℝ) := by
      have : (i : ℝ) < q.natDegree := by exact_mod_cast hi
      linarith
    have hcast : ((q.natDegree - i : ℕ) : ℝ) = (q.natDegree - i : ℝ) := by
      rw [Nat.cast_sub hi.le]
    calc ‖q.coeff i‖ = (‖q.coeff i‖ ^ (1 / (q.natDegree - i : ℝ))) ^ ((q.natDegree - i : ℕ) : ℝ) := by
          rw [← Real.rpow_mul (norm_nonneg _), hcast, one_div, inv_mul_cancel₀ hpos.ne', Real.rpow_one]
      _ ≤ ‖y‖ ^ ((q.natDegree - i : ℕ) : ℝ) :=
          Real.rpow_le_rpow (by positivity) h1 (Nat.cast_nonneg _)
      _ = ‖y‖ ^ (q.natDegree - i) := Real.rpow_natCast _ _
  · rw [hi, Nat.sub_self, pow_zero, (minpoly.monic (Algebra.IsIntegral.isIntegral y)).coeff_natDegree,
      norm_one]

theorem norm_minpoly_coeff_zero (y : PadicAlgCl p) :
    ‖(minpoly ℚ_[p] y).coeff 0‖ = ‖y‖ ^ (minpoly ℚ_[p] y).natDegree := by
  have h := spectralNorm.spectralNorm_eq_norm_coeff_zero_rpow (K := ℚ_[p]) (L := PadicAlgCl p) y
  rw [PadicAlgCl.spectralNorm_eq] at h
  have hd : (0 : ℝ) < (minpoly ℚ_[p] y).natDegree := by exact_mod_cast natDegree_minpoly_pos y
  rw [h, ← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _), one_div, inv_mul_cancel₀ hd.ne',
    Real.rpow_one]

theorem eq_of_no_dominant {d : ℕ} (hd : 1 ≤ d) {Fa Fb μ ρk : ℝ} (hFa : 0 < Fa) (hFb : 0 < Fb)
    (hμ : 0 < μ) (hρk : 0 < ρk) (G : ℕ → ℝ) (hG : ∀ i ≤ d, 0 ≤ G i ∧ G i ≤ ρk * μ ^ (d - i))
    (hG0 : G 0 = ρk * μ ^ d) (hGd : G d = ρk)
    (hnd : ∀ j ∈ Finset.range (d + 1), 0 < G j * Fa ^ j * Fb ^ (d - j) →
      ¬ ∀ i ∈ Finset.range (d + 1), i ≠ j →
        G i * Fa ^ i * Fb ^ (d - i) < G j * Fa ^ j * Fb ^ (d - j)) :
    Fa = μ * Fb := by
  rcases lt_trichotomy Fa (μ * Fb) with hlt | heq | hgt
  · exfalso
    refine hnd 0 (Finset.mem_range.2 (by omega)) ?_ fun i hi hi0 => ?_
    · rw [hG0]; positivity
    · have hid : i ≤ d := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
      obtain ⟨hG1, hG2⟩ := hG i hid
      have hpow : Fa ^ i < (μ * Fb) ^ i := pow_lt_pow_left₀ hlt hFa.le hi0
      have e1 : ρk * μ ^ (d - i) * (μ * Fb) ^ i * Fb ^ (d - i) = ρk * μ ^ d * Fb ^ d := by
        rw [mul_pow]
        have h1 : μ ^ (d - i) * μ ^ i = μ ^ d := by rw [← pow_add, Nat.sub_add_cancel hid]
        have h2 : Fb ^ i * Fb ^ (d - i) = Fb ^ d := by rw [← pow_add, Nat.add_sub_cancel' hid]
        calc ρk * μ ^ (d - i) * (μ ^ i * Fb ^ i) * Fb ^ (d - i)
            = ρk * (μ ^ (d - i) * μ ^ i) * (Fb ^ i * Fb ^ (d - i)) := by ring
          _ = _ := by rw [h1, h2]
      rw [hG0, Nat.sub_zero, pow_zero, mul_one, ← e1]
      calc G i * Fa ^ i * Fb ^ (d - i) ≤ ρk * μ ^ (d - i) * Fa ^ i * Fb ^ (d - i) := by
            gcongr
        _ < ρk * μ ^ (d - i) * (μ * Fb) ^ i * Fb ^ (d - i) := by
            have : 0 < ρk * μ ^ (d - i) := by positivity
            have : 0 < Fb ^ (d - i) := by positivity
            gcongr
  · exact heq
  · exfalso
    refine hnd d (Finset.mem_range.2 (by omega)) ?_ fun i hi hid' => ?_
    · rw [hGd, Nat.sub_self, pow_zero, mul_one]; positivity
    · have hid : i < d := lt_of_le_of_ne (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)) hid'
      obtain ⟨hG1, hG2⟩ := hG i hid.le
      have hpow : (μ * Fb) ^ (d - i) < Fa ^ (d - i) := pow_lt_pow_left₀ hgt (by positivity) (by omega)
      have e1 : ρk * Fa ^ i * Fa ^ (d - i) = ρk * Fa ^ d := by
        rw [mul_assoc, ← pow_add, Nat.add_sub_cancel' hid.le]
      rw [hGd, Nat.sub_self, pow_zero, mul_one, ← e1]
      calc G i * Fa ^ i * Fb ^ (d - i) ≤ ρk * μ ^ (d - i) * Fa ^ i * Fb ^ (d - i) := by gcongr
        _ = ρk * Fa ^ i * (μ * Fb) ^ (d - i) := by rw [mul_pow]; ring
        _ < ρk * Fa ^ i * Fa ^ (d - i) := by
            have : 0 < ρk * Fa ^ i := by positivity
            gcongr

end ACris

end GroundTheory.PAdicHodge
