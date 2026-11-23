import Mathlib
import GroundTheory.PAdicHodge.BCrisNewtonKey
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

namespace ACris

open _root_.WittVector Polynomial

variable {p : ℕ} [hp : Fact p.Prime]

local notation "𝔹" => BDeRhamPlus (normInteger ℂ_[p]) p
local notation "𝔹dR" => BDeRham (normInteger ℂ_[p]) p

theorem exists_mul_pow_eq_of_away {R B : Type*} [CommRing R] [CommRing B] {r : R} (g : R →+* B)
    (f : Localization.Away r →+* B) (hfg : ∀ a, f (algebraMap R _ a) = g a)
    (x : Localization.Away r) : ∃ (w : R) (n : ℕ), f x * g r ^ n = g w := by
  obtain ⟨n, w, hw⟩ := IsLocalization.Away.surj r x
  refine ⟨w, n, ?_⟩
  have := congrArg f hw
  rwa [map_mul, map_pow, hfg, hfg] at this

def IsACrisFraction (y : PadicAlgCl p) : Prop :=
  ∃ a b : ACris ℂ_[p] p, b ≠ 0 ∧ iota ℂ_[p] p a = algClToBdR p y * iota ℂ_[p] p b

theorem iota_ne_zero {b : ACris ℂ_[p] p} (hb : b ≠ 0) : iota ℂ_[p] p b ≠ 0 :=
  fun h => hb (iota_injective (by rw [h, map_zero]))

theorem one_ne_zero_aCris : (1 : ACris ℂ_[p] p) ≠ 0 := by
  intro h
  have := congrArg (iota ℂ_[p] p) h
  rw [map_one, map_zero] at this
  exact one_ne_zero this

theorem mul_ne_zero_aCris {b c : ACris ℂ_[p] p} (hb : b ≠ 0) (hc : c ≠ 0) : b * c ≠ 0 := by
  intro h
  have := congrArg (iota ℂ_[p] p) h
  rw [map_mul, map_zero] at this
  exact mul_ne_zero (iota_ne_zero hb) (iota_ne_zero hc) this

theorem IsACrisFraction.mul {y z : PadicAlgCl p} (hy : IsACrisFraction y) (hz : IsACrisFraction z) :
    IsACrisFraction (y * z) := by
  obtain ⟨a, b, hb, h⟩ := hy
  obtain ⟨a', b', hb', h'⟩ := hz
  refine ⟨a * a', b * b', mul_ne_zero_aCris hb hb', ?_⟩
  rw [map_mul, map_mul, map_mul, h, h']
  ring

theorem IsACrisFraction.sub {y z : PadicAlgCl p} (hy : IsACrisFraction y) (hz : IsACrisFraction z) :
    IsACrisFraction (y - z) := by
  obtain ⟨a, b, hb, h⟩ := hy
  obtain ⟨a', b', hb', h'⟩ := hz
  refine ⟨a * b' - a' * b, b * b', mul_ne_zero_aCris hb hb', ?_⟩
  rw [map_sub, map_mul, map_mul, map_mul, map_sub, h, h']
  ring

theorem IsACrisFraction.pow {y : PadicAlgCl p} (hy : IsACrisFraction y) (n : ℕ) :
    IsACrisFraction (y ^ n) := by
  induction n with
  | zero => exact ⟨1, 1, one_ne_zero_aCris, by rw [pow_zero, map_one, map_one, one_mul]⟩
  | succ n ih => rw [pow_succ]; exact ih.mul hy

theorem isACrisFraction_of_mem {u : PadicAlgCl p} (hu : u ∈ unramifiedClosure p) :
    IsACrisFraction u := by
  obtain ⟨x, hx⟩ := mem_algClInBCrisPlus.1 (unramifiedClosure_le hu)
  obtain ⟨w, n, hw⟩ := exists_mul_pow_eq_of_away (iota ℂ_[p] p) (iotaPlus ℂ_[p] p)
    (fun a => iotaPlus_algebraMap a) x
  refine ⟨w, (p : ACris ℂ_[p] p) ^ n, fun h0 => ?_, ?_⟩
  · have := congrArg (iota ℂ_[p] p) h0
    rw [map_pow, map_natCast, map_zero, ← map_natCast (algebraMap ℚ_[p] 𝔹) p, ← map_pow] at this
    exact pow_ne_zero n (Nat.cast_ne_zero.2 hp.out.ne_zero : (p : ℚ_[p]) ≠ 0)
      ((algebraMap ℚ_[p] 𝔹).injective (by rw [this, map_zero]))
  · rw [← hw, hx, map_pow]

theorem IsACrisFraction.exists_norm_eq_zpow {y : PadicAlgCl p} (hy : IsACrisFraction y)
    (hy0 : y ≠ 0) : ∃ D : ℤ, ‖y‖ = ‖(p : PadicAlgCl p)‖ ^ D := by
  obtain ⟨a, b, hb, h⟩ := hy
  exact exists_norm_eq_zpow_of_iota_eq hy0 hb h

theorem IsACrisFraction.norm_le {y : PadicAlgCl p} (hy : IsACrisFraction y) (h1 : ‖y‖ < 1) :
    ‖y‖ ≤ ‖(p : PadicAlgCl p)‖ := by
  by_cases hy0 : y = 0
  · rw [hy0, norm_zero]; exact norm_nonneg _
  obtain ⟨D, hD⟩ := hy.exists_norm_eq_zpow hy0
  have hp0 : 0 < ‖(p : PadicAlgCl p)‖ := by rw [norm_p_algCl]; exact inv_p_pos
  have hp1 : ‖(p : PadicAlgCl p)‖ ≤ 1 := by rw [norm_p_algCl]; exact inv_p_lt_one.le
  rw [hD]
  by_cases hD1 : 1 ≤ D
  · exact (zpow_le_zpow_right_of_le_one₀ hp0 hp1 hD1).trans_eq (zpow_one _)
  · exfalso
    have : (1 : ℝ) ≤ ‖(p : PadicAlgCl p)‖ ^ D := by
      rw [← zpow_zero ‖(p : PadicAlgCl p)‖]
      exact zpow_le_zpow_right_of_le_one₀ hp0 hp1 (by omega)
    rw [← hD] at this
    linarith

theorem norm_sub_pow_sub_le {F : Type*} [NormedField F] [IsUltrametricDist F] (hpF : ‖(p : F)‖ < 1)
    {a b : F} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) (k : ℕ) :
    ‖(a - b) ^ p ^ k - (a ^ p ^ k - b ^ p ^ k)‖ ≤ ‖(p : F)‖ := by
  set O := normInteger F
  set a' : O := ⟨a, mem_normInteger.2 ha⟩
  set b' : O := ⟨b, mem_normInteger.2 hb⟩
  have hnu : (p : O) ∈ nonunits O := by
    rw [mem_nonunits_iff]
    rintro ⟨u, hu⟩
    have h1 := congrArg (fun z : O => (z : F)) u.mul_inv
    simp only [MulMemClass.coe_mul, OneMemClass.coe_one] at h1
    rw [hu] at h1
    push_cast at h1
    have h2 := congrArg norm h1
    rw [norm_mul, norm_one] at h2
    have h3 : ‖(((u⁻¹ : Oˣ) : O) : F)‖ ≤ 1 := mem_normInteger.1 (u⁻¹ : Oˣ).val.2
    nlinarith [norm_nonneg ((p : F))]
  haveI := CharP.quotient O p hnu
  have h := sub_pow_char_pow (p := p) (n := k) (Ideal.Quotient.mk (Ideal.span {(p : O)}) a')
    (Ideal.Quotient.mk (Ideal.span {(p : O)}) b')
  rw [← map_sub, ← map_pow, ← map_pow, ← map_pow, ← map_sub, Ideal.Quotient.eq] at h
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 h
  have h4 := congrArg (fun z : O => (z : F)) hc
  push_cast at h4
  rw [← h4, norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (mem_normInteger.1 c.2)

theorem norm_p_algCl_lt_one : ‖(p : PadicAlgCl p)‖ < 1 := by
  rw [norm_p_algCl]; exact inv_p_lt_one

theorem exists_approx_of_isACrisFraction (m : ℕ) :
    ∀ y : PadicAlgCl p, IsACrisFraction y → ‖y‖ ≤ 1 →
      ∃ u ∈ unramifiedClosure p, ‖y - u‖ ≤ ‖(p : PadicAlgCl p)‖ ^ m := by
  induction m with
  | zero => intro y _ hy1; exact ⟨0, zero_mem _, by rw [sub_zero, pow_zero]; exact hy1⟩
  | succ m ih =>
    intro y hy hy1
    have hp1 := norm_p_algCl_lt_one (p := p)
    obtain ⟨k₀, k₁, hk, hkk⟩ := exists_lt_norm_pow_sub_lt hy1 one_pos (fun k => p ^ k)
    set r := k₁ - k₀ with hr
    have hr1 : 1 ≤ r := by omega
    set z := y ^ p ^ r - y with hz
    have hyr : ‖y ^ p ^ r‖ ≤ 1 := by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hy1
    have hbin := norm_sub_pow_sub_le hp1 hyr hy1 k₀
    have hk1 : (y ^ p ^ r) ^ p ^ k₀ = y ^ p ^ k₁ := by
      rw [← pow_mul, ← pow_add, hr, Nat.sub_add_cancel hk.le]
    rw [hk1] at hbin
    have hz1 : ‖z ^ p ^ k₀‖ < 1 := by
      have e : z ^ p ^ k₀ = (z ^ p ^ k₀ - (y ^ p ^ k₁ - y ^ p ^ k₀)) + (y ^ p ^ k₁ - y ^ p ^ k₀) := by ring
      rw [e]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt (hbin.trans_lt hp1) hkk)
    have hz2 : ‖z‖ < 1 := by
      rw [norm_pow] at hz1
      exact (pow_lt_one_iff_of_nonneg (norm_nonneg _) (pow_ne_zero _ hp.out.ne_zero)).1 hz1
    have hzf : IsACrisFraction z := (hy.pow _).sub hy
    have hz3 := hzf.norm_le hz2

    have hyC : ‖(y : ℂ_[p])‖ ≤ 1 := by rw [PadicComplex.norm_extends]; exact hy1
    have hzC : ‖(y : ℂ_[p]) ^ p ^ r - (y : ℂ_[p])‖ ≤ ‖(p : ℂ_[p])‖ ^ 1 := by
      rw [pow_one, ← PadicComplex.coe_natCast, PadicComplex.norm_extends]
      have : (y : ℂ_[p]) ^ p ^ r - (y : ℂ_[p]) = ((y ^ p ^ r - y : PadicAlgCl p) : ℂ_[p]) := by
        simp only [PadicComplex.coe_eq, map_sub, map_pow]
      rw [this, PadicComplex.norm_extends]
      exact hz3
    obtain ⟨u₀, hu₀, hu₀y⟩ := exists_approx_of_pow_sub hyC hr1 hzC
    rw [pow_one, ← PadicComplex.coe_natCast, PadicComplex.norm_extends,
      show (y : ℂ_[p]) - (u₀ : ℂ_[p]) = ((y - u₀ : PadicAlgCl p) : ℂ_[p]) by
        simp only [PadicComplex.coe_eq, map_sub],
      PadicComplex.norm_extends] at hu₀y

    have hpne : (p : PadicAlgCl p) ≠ 0 := Nat.cast_ne_zero.2 hp.out.ne_zero
    set y' := (y - u₀) * (p : PadicAlgCl p)⁻¹ with hy'
    have hpinv : (p : PadicAlgCl p)⁻¹ ∈ unramifiedClosure p := inv_mem (natCast_mem _ p)
    have hy'f : IsACrisFraction y' := (hy.sub (isACrisFraction_of_mem hu₀)).mul
      (isACrisFraction_of_mem hpinv)
    have hnp0 : 0 < ‖(p : PadicAlgCl p)‖ := norm_pos_iff.2 hpne
    have hy'1 : ‖y'‖ ≤ 1 := by
      rw [hy', norm_mul, norm_inv]
      rw [← div_eq_mul_inv]
      exact (div_le_one hnp0).2 hu₀y
    obtain ⟨u', hu', hu'y⟩ := ih y' hy'f hy'1
    refine ⟨u₀ + (p : PadicAlgCl p) * u', add_mem hu₀ (mul_mem (natCast_mem _ p) hu'), ?_⟩
    have e : y - (u₀ + (p : PadicAlgCl p) * u') = (p : PadicAlgCl p) * (y' - u') := by
      rw [hy']; field_simp; ring
    rw [e, norm_mul, pow_succ, mul_comm]
    exact mul_le_mul_of_nonneg_right hu'y (norm_nonneg _)

theorem IsACrisFraction.mem_unramifiedClosure {y : PadicAlgCl p} (hy : IsACrisFraction y) :
    y ∈ unramifiedClosure p := by
  have hpne : (p : PadicAlgCl p) ≠ 0 := Nat.cast_ne_zero.2 hp.out.ne_zero
  have hp1 := norm_p_algCl_lt_one (p := p)
  have hnp0 : 0 < ‖(p : PadicAlgCl p)‖ := norm_pos_iff.2 hpne
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (inv_pos.2 (zero_lt_one.trans_le (le_max_left 1 ‖y‖)))
    hp1
  set y' := (p : PadicAlgCl p) ^ n * y
  have hy'1 : ‖y'‖ ≤ 1 := by
    rw [norm_mul, norm_pow]
    calc ‖(p : PadicAlgCl p)‖ ^ n * ‖y‖ ≤ (max 1 ‖y‖)⁻¹ * max 1 ‖y‖ :=
          mul_le_mul hn.le (le_max_right _ _) (norm_nonneg _) (by positivity)
      _ = 1 := inv_mul_cancel₀ (zero_lt_one.trans_le (le_max_left 1 ‖y‖)).ne'
  have hy'f : IsACrisFraction y' := (isACrisFraction_of_mem (pow_mem (natCast_mem _ p) n)).mul hy
  have hy' : y' ∈ unramifiedClosure p := mem_unramifiedClosure_of_forall_approx fun m =>
    exists_approx_of_isACrisFraction m y' hy'f hy'1
  have : y = ((p : PadicAlgCl p) ^ n)⁻¹ * y' := by
    rw [← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hpne), one_mul]
  rw [this]
  exact mul_mem (inv_mem (pow_mem (natCast_mem _ p) n)) hy'

end ACris

end GroundTheory.PAdicHodge
