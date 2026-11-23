import Formalism.WachLatticeTwists.LagrangeExtensionCocycles.ExtensionCocycleProofs.MemSpanOfFrobeniusMemSpan
import Formalism.ResultantValuation.ResultantAdjugateProofs.Window

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.N2

open Polynomial

theorem aH_le_eWA (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : ℓ ≠ 2) (H : ℕ) :
    (H + (ℓ - 2)) / (ℓ - 1) + padicValNat ℓ ((H + (ℓ - 2)) / (ℓ - 1)).factorial ≤ eWA ℓ H := by
  set a := (H + (ℓ - 2)) / (ℓ - 1) with ha
  have hp := (Fact.out : ℓ.Prime)
  have hℓ3 : 3 ≤ ℓ := by have := hp.two_le; omega
  have hv : (ℓ - 1) * padicValNat ℓ a.factorial ≤ a := by
    rw [sub_one_mul_padicValNat_factorial]
    exact Nat.sub_le _ _
  have haH : (ℓ - 1) * a ≤ H + (ℓ - 2) := Nat.mul_div_le (H + (ℓ - 2)) (ℓ - 1)
  have hcast : ((ℓ - 1 : ℕ) : ℝ) = (ℓ : ℝ) - 1 := by rw [Nat.cast_sub (by omega), Nat.cast_one]
  have hcast2 : ((ℓ - 2 : ℕ) : ℝ) = (ℓ : ℝ) - 2 := by rw [Nat.cast_sub (by omega)]; norm_num
  have hvR : ((ℓ : ℝ) - 1) * (padicValNat ℓ a.factorial : ℝ) ≤ a := by
    rw [← hcast]; exact_mod_cast hv
  have haR : ((ℓ : ℝ) - 1) * (a : ℝ) ≤ (H : ℝ) + ((ℓ : ℝ) - 1) - 1 := by
    have h0 : ((ℓ - 1 : ℕ) : ℝ) * (a : ℝ) ≤ (H : ℝ) + ((ℓ - 2 : ℕ) : ℝ) := by exact_mod_cast haH
    rw [hcast, hcast2] at h0
    linarith
  have hL : (0 : ℝ) < (ℓ : ℝ) - 1 := by
    have : (3 : ℝ) ≤ ℓ := by exact_mod_cast hℓ3
    linarith
  have hlog : 0 ≤ Real.logb ℓ ((H : ℝ) + 1) :=
    Real.logb_nonneg (by exact_mod_cast hp.one_lt) (by linarith [(Nat.cast_nonneg H : (0 : ℝ) ≤ H)])
  have key : ((ℓ : ℝ) - 1) ^ 2 * ((a : ℝ) + (padicValNat ℓ a.factorial : ℝ)) ≤
      (H : ℝ) * ℓ + ((ℓ : ℝ) - 1) ^ 2 - 1 := by
    nlinarith [mul_le_mul_of_nonneg_left hvR hL.le, mul_le_mul_of_nonneg_left haR (by linarith : (0 : ℝ) ≤ ℓ)]
  have hL2 : 0 < ((ℓ : ℝ) - 1) ^ 2 := by positivity
  have h1 : (a : ℝ) + (padicValNat ℓ a.factorial : ℝ) ≤
      ((H : ℝ) * ℓ + ((ℓ : ℝ) - 1) ^ 2 - 1) / ((ℓ : ℝ) - 1) ^ 2 := by
    rw [le_div_iff₀ hL2]; linarith [key]
  have h2 : ((H : ℝ) * ℓ + ((ℓ : ℝ) - 1) ^ 2 - 1) / ((ℓ : ℝ) - 1) ^ 2 ≤ (H : ℝ) * ℓ / ((ℓ : ℝ) - 1) ^ 2 + 1 := by
    rw [div_le_iff₀ hL2, add_mul, div_mul_cancel₀ _ hL2.ne']
    linarith
  unfold eWA
  apply Nat.le_floor
  push_cast
  linarith

theorem prod_sub_one_dvd (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : ℓ ≠ 2) (u : ℤ_[ℓ]ˣ)
    (hv : PadicInt.valuation ((u : ℤ_[ℓ]) - 1) = 1) (a : ℕ) :
    (∏ i ∈ Finset.Icc 1 a, (1 - (u : ℤ_[ℓ]) ^ i)) ∣ (ℓ : ℤ_[ℓ]) ^ (a + padicValNat ℓ a.factorial) := by
  have hπ : Prime (ℓ : ℤ_[ℓ]) := PadicInt.prime_p
  have hp := (Fact.out : ℓ.Prime)
  have hodd : Odd ℓ := hp.odd_of_ne_two hℓ
  have hnd_unit : ∀ w : ℤ_[ℓ], IsUnit w → ¬ (ℓ : ℤ_[ℓ]) ∣ w := fun w hw hd =>
    hπ.not_unit (isUnit_of_dvd_unit hd hw)
  have hunit_of : ∀ w : ℤ_[ℓ], ¬ (ℓ : ℤ_[ℓ]) ∣ w → IsUnit w := by
    intro w hw
    by_contra hnu
    apply hw
    have hm : w ∈ IsLocalRing.maximalIdeal ℤ_[ℓ] := (IsLocalRing.mem_maximalIdeal w).2 (mem_nonunits_iff.2 hnu)
    rw [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton] at hm
    exact hm
  have hne : (u : ℤ_[ℓ]) - 1 ≠ 0 := by
    intro h0
    rw [h0, PadicInt.valuation_zero] at hv
    exact absurd hv (by norm_num)
  have hspec := PadicInt.unitCoeff_spec hne
  rw [hv, pow_one] at hspec
  have hdiv1 : (ℓ : ℤ_[ℓ]) ∣ (u : ℤ_[ℓ]) - 1 := by
    rw [hspec]
    exact dvd_mul_left _ _
  have hA : emultiplicity (ℓ : ℤ_[ℓ]) ((u : ℤ_[ℓ]) - 1) = ((1 : ℕ) : ℕ∞) := by
    rw [emultiplicity_eq_coe]
    refine ⟨by rw [pow_one]; exact hdiv1, fun h2 => ?_⟩
    rw [hspec, pow_succ, pow_one] at h2
    exact hnd_unit _ (Units.isUnit _) ((mul_dvd_mul_iff_right hπ.ne_zero).1 h2)
  have hnu : ¬ (ℓ : ℤ_[ℓ]) ∣ (u : ℤ_[ℓ]) := hnd_unit _ u.isUnit
  have hnat : ∀ m : ℕ, ¬ ℓ ∣ m → ¬ (ℓ : ℤ_[ℓ]) ∣ (m : ℤ_[ℓ]) := by
    intro m hm hd
    have hcop : Nat.Coprime ℓ m := (Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd hp).2 hm).symm)
    have hg : Int.gcd (ℓ : ℤ) (m : ℤ) = 1 := by
      have := Int.gcd_natCast_natCast ℓ m
      rw [this]
      exact hcop
    have hz : (1 : ℤ) = ℓ * Int.gcdA ℓ m + m * Int.gcdB ℓ m := by
      rw [← Int.gcd_eq_gcd_ab, hg]
      rfl
    have h1 := congrArg (Int.cast : ℤ → ℤ_[ℓ]) hz
    push_cast at h1
    apply hπ.not_unit
    apply isUnit_of_dvd_one
    rw [h1]
    exact dvd_add (dvd_mul_right _ _) (dvd_mul_of_dvd_left hd _)
  have hB : ∀ i : ℕ, 1 ≤ i → emultiplicity (ℓ : ℤ_[ℓ]) ((u : ℤ_[ℓ]) ^ i - 1) = ((1 + padicValNat ℓ i : ℕ) : ℕ∞) := by
    intro i hi
    obtain ⟨k, m, hm, hkm⟩ := Nat.exists_eq_pow_mul_and_not_dvd (n := i) (by omega) ℓ hp.ne_one
    have hm0 : m ≠ 0 := by
      rintro rfl
      exact hm (dvd_zero ℓ)
    have hval : padicValNat ℓ i = k := by
      rw [hkm, padicValNat.mul (pow_ne_zero _ hp.ne_zero) hm0, padicValNat.prime_pow,
        padicValNat.eq_zero_of_not_dvd hm, add_zero]
    have hdivk : (ℓ : ℤ_[ℓ]) ∣ (u : ℤ_[ℓ]) ^ (ℓ ^ k) - 1 := by
      have := sub_dvd_pow_sub_pow (u : ℤ_[ℓ]) 1 (ℓ ^ k)
      rw [one_pow] at this
      exact dvd_trans hdiv1 this
    have hnuk : ¬ (ℓ : ℤ_[ℓ]) ∣ (u : ℤ_[ℓ]) ^ (ℓ ^ k) := hnd_unit _ (u.isUnit.pow _)
    have e1 := emultiplicity_pow_sub_pow_of_prime hπ (x := (u : ℤ_[ℓ]) ^ (ℓ ^ k)) (y := 1) (by simpa using hdivk)
      hnuk (n := m) (hnat m hm)
    have e2 := emultiplicity_pow_prime_pow_sub_pow_prime_pow (y := (1 : ℤ_[ℓ])) (by simpa using hπ) hodd
      (by simpa using hdiv1) hnu k
    have e3 : (u : ℤ_[ℓ]) ^ i - 1 = ((u : ℤ_[ℓ]) ^ (ℓ ^ k)) ^ m - 1 ^ m := by
      rw [hkm, pow_mul, one_pow]
    rw [one_pow] at e2
    rw [hval, e3, e1, e2, hA]
    norm_cast
  have hF : ∀ i : ℕ, 1 ≤ i → (1 - (u : ℤ_[ℓ]) ^ i) ∣ (ℓ : ℤ_[ℓ]) ^ (1 + padicValNat ℓ i) := by
    intro i hi
    have hE : emultiplicity (ℓ : ℤ_[ℓ]) (1 - (u : ℤ_[ℓ]) ^ i) = ((1 + padicValNat ℓ i : ℕ) : ℕ∞) := by
      rw [← neg_sub, emultiplicity_neg, hB i hi]
    obtain ⟨hd, hnd⟩ := (emultiplicity_eq_coe.1 hE)
    obtain ⟨w, hw⟩ := hd
    have hwu : IsUnit w := by
      apply hunit_of
      rintro ⟨c, rfl⟩
      apply hnd
      rw [hw, pow_succ]
      exact mul_dvd_mul_left _ (dvd_mul_right _ _)
    refine ⟨(hwu.unit⁻¹ : ℤ_[ℓ]ˣ), ?_⟩
    rw [hw, mul_assoc, IsUnit.mul_val_inv, mul_one]
  induction a with
  | zero => simp
  | succ a ih =>
    rw [Finset.prod_Icc_succ_top (by omega), Nat.factorial_succ,
      padicValNat.mul (by omega) (Nat.factorial_ne_zero a)]
    have e : a + 1 + (padicValNat ℓ (a + 1) + padicValNat ℓ a.factorial) =
        (a + padicValNat ℓ a.factorial) + (1 + padicValNat ℓ (a + 1)) := by ring
    rw [e, pow_add (ℓ : ℤ_[ℓ]) (a + padicValNat ℓ a.factorial) (1 + padicValNat ℓ (a + 1))]
    exact mul_dvd_mul ih (hF (a + 1) (by omega))

theorem unit_lemma_case_a_level_zero : StatWA0 := by
  intro ℓ _ hℓ A _ _ G D _ _ _ _ P H hv hK
  set a := (H + (ℓ - 2)) / (ℓ - 1) with ha
  have h1 := mem_span_of_frobenius_mem_span ℓ A G D P a 0 (Nat.zero_le _) hK
  have hdvd : (∏ k ∈ Finset.Ioc 0 a, ((G.u : ℤ_[ℓ]) ^ k - 1)) ∣
      (ℓ : ℤ_[ℓ]) ^ (a + padicValNat ℓ a.factorial) := by
    have h2 := prod_sub_one_dvd ℓ hℓ G.u hv a
    have e : ∏ k ∈ Finset.Ioc 0 a, ((G.u : ℤ_[ℓ]) ^ k - 1) =
        (-1) ^ a * ∏ i ∈ Finset.Icc 1 a, (1 - (G.u : ℤ_[ℓ]) ^ i) := by
      have hI : Finset.Ioc 0 a = Finset.Icc 1 a := by
        ext i
        simp only [Finset.mem_Ioc, Finset.mem_Icc]
        omega
      rw [hI]
      have hneg : ∀ i ∈ Finset.Icc 1 a, ((G.u : ℤ_[ℓ]) ^ i - 1) = -(1 - (G.u : ℤ_[ℓ]) ^ i) :=
        fun i _ => by ring
      rw [Finset.prod_congr rfl hneg, Finset.prod_neg, Nat.card_Icc, Nat.add_sub_cancel]
    rw [e]
    exact (isUnit_neg_one.pow a).mul_left_dvd.2 h2
  have h3 := P.kills_pow_of_dvd hdvd h1
  simp only [pow_zero, mul_one] at h3
  exact ⟨h3, P.kills_of_dvd (pow_dvd_pow _ (aH_le_eWA ℓ hℓ H)) h3⟩

end Formalism.RepresentationBoundsCohomology.N2
