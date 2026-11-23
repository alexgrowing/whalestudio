import Formalism.PeriodIntegrals.GoodTwo
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.DyadicStableLattices.ChainPA

noncomputable section
open scoped ComplexConjugate

namespace PI.GoodTwo.ChainBetweenPairs

open Formalism.L2.Th1.CM (HasCMBy omegaK)
open Formalism.L2.Th1.F (scalePair MulStable)

theorem omega_sq (d : ℕ) (hd : d % 4 = 3) :
    omegaK d ^ 2 = omegaK d - (((d + 1) / 4 : ℕ) : ℂ) := by
  have hdiv : (((d + 1) / 4 : ℕ) : ℂ) = ((d : ℂ) + 1) / 4 := by
    have h4 : 4 ∣ d + 1 := by omega
    rw [Nat.cast_div h4 (by norm_num)]
    push_cast
    ring
  have hs : ((Real.sqrt d : ℝ) : ℂ) ^ 2 = d := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg d)]
    push_cast
    rfl
  have hI : Complex.I ^ 2 = -1 := Complex.I_sq
  unfold omegaK
  rw [hdiv]
  linear_combination (((Real.sqrt d : ℝ) : ℂ) ^ 2 / 4) * hI - (1 / 4 : ℂ) * hs

theorem conj_omega (d : ℕ) : conj (omegaK d) = 1 - omegaK d := by
  unfold omegaK
  simp [map_div₀, map_add, map_mul, Complex.conj_I, Complex.conj_ofReal, map_ofNat]
  ring

theorem int_mul_mem (L : PeriodPair) (n : ℤ) {z : ℂ} (hz : z ∈ L.lattice) :
    (n : ℂ) * z ∈ L.lattice := by
  rw [← zsmul_eq_mul]
  exact zsmul_mem hz n

theorem pow_two_mul_mem (L : PeriodPair) (i : ℕ) {z : ℂ} (hz : z ∈ L.lattice) :
    (2 : ℂ) ^ i * z ∈ L.lattice := by
  have h := int_mul_mem L (2 ^ i) hz
  push_cast at h
  exact h

theorem stab (d : ℕ) (L : PeriodPair) (hL : HasCMBy d L) (m n : ℤ) {z : ℂ} (hz : z ∈ L.lattice) :
    ((m : ℂ) + n * omegaK d) * z ∈ L.lattice := by
  rw [add_mul, mul_assoc]
  exact add_mem (int_mul_mem L m hz) (int_mul_mem L n (hL z hz))

theorem not_half (d : ℕ) (L : PeriodPair) (m n : ℤ) (hn : Odd n) :
    ¬ MulStable L (((m : ℂ) + n * omegaK d) / 2) := by
  intro hS
  obtain ⟨t, N, ht, -, -⟩ := Formalism.L2.Th1.F.mulStableIntegral L _ hS
  simp only [map_div₀, map_add, map_mul, map_intCast, map_ofNat, conj_omega] at ht
  have h2 : ((2 * m + n : ℤ) : ℂ) = ((2 * t : ℤ) : ℂ) := by
    push_cast
    linear_combination 2 * ht
  have h3 : 2 * m + n = 2 * t := by exact_mod_cast h2
  obtain ⟨k, rfl⟩ := hn
  omega

theorem half_mem (L : PeriodPair) (w : ℂ) (p q : ℤ) (hw : (p : ℂ) * L.ω₁ + q * L.ω₂ = 2 * w)
    (h : (p : ZMod 2) = 0 ∧ (q : ZMod 2) = 0) : w ∈ L.lattice := by
  obtain ⟨hp, hq⟩ := h
  obtain ⟨p', rfl⟩ : (2 : ℤ) ∣ p := (ZMod.intCast_zmod_eq_zero_iff_dvd p 2).mp hp
  obtain ⟨q', rfl⟩ : (2 : ℤ) ∣ q := (ZMod.intCast_zmod_eq_zero_iff_dvd q 2).mp hq
  have hw' : w = (p' : ℂ) * L.ω₁ + q' * L.ω₂ := by
    push_cast at hw
    linear_combination (-1 / 2 : ℂ) * hw
  rw [hw']
  exact add_mem (int_mul_mem L p' L.ω₁_mem_lattice) (int_mul_mem L q' L.ω₂_mem_lattice)

theorem two_tors (L : PeriodPair) (π : ℂ) (hπ : ¬ MulStable L (π / 2)) (hπL : MulStable L π)
    {u v : ℂ} (hu1 : π * u ∈ L.lattice) (hu2 : 2 * u ∈ L.lattice) (hu3 : u ∉ L.lattice)
    (hv1 : π * v ∈ L.lattice) (hv2 : 2 * v ∈ L.lattice) (hv3 : v ∉ L.lattice) :
    u - v ∈ L.lattice := by
  by_contra huv
  apply hπ
  obtain ⟨a, b, hab⟩ := PeriodPair.mem_lattice.1 hu2
  obtain ⟨c, e, hce⟩ := PeriodPair.mem_lattice.1 hv2
  have key : ∀ p q r s : ZMod 2, ¬ (p = 0 ∧ q = 0) → ¬ (r = 0 ∧ s = 0) →
      ¬ (p - r = 0 ∧ q - s = 0) → p * s - q * r ≠ 0 := by decide
  have hdet : ((a * e - b * c : ℤ) : ZMod 2) ≠ 0 := by
    push_cast
    refine key _ _ _ _ (fun h => hu3 (half_mem L u a b hab h)) (fun h => hv3 (half_mem L v c e hce h))
      (fun h => huv (half_mem L (u - v) (a - c) (b - e) ?_ ?_))
    · push_cast
      linear_combination hab - hce
    · push_cast
      exact h
  have hodd : Odd (a * e - b * c) := by
    rw [← Int.not_even_iff_odd, even_iff_two_dvd]
    intro h2
    exact hdet ((ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).2 (by exact_mod_cast h2))
  obtain ⟨m, hm⟩ := hodd
  have hmC : (a : ℂ) * e - b * c = 2 * m + 1 := by exact_mod_cast hm
  have e1 : L.ω₁ / 2 = (e : ℂ) * u - b * v - m * L.ω₁ := by
    linear_combination ((e : ℂ) / 2) * hab - ((b : ℂ) / 2) * hce - (L.ω₁ / 2) * hmC
  have e2 : L.ω₂ / 2 = (a : ℂ) * v - c * u - m * L.ω₂ := by
    linear_combination ((a : ℂ) / 2) * hce - ((c : ℂ) / 2) * hab - (L.ω₂ / 2) * hmC
  have h1 : π * (L.ω₁ / 2) ∈ L.lattice := by
    have f : π * ((e : ℂ) * u - b * v - m * L.ω₁) = (e : ℂ) * (π * u) - b * (π * v) - m * (π * L.ω₁) := by
      ring
    rw [e1, f]
    exact sub_mem (sub_mem (int_mul_mem L e hu1) (int_mul_mem L b hv1))
      (int_mul_mem L m (hπL _ L.ω₁_mem_lattice))
  have h2 : π * (L.ω₂ / 2) ∈ L.lattice := by
    have f : π * ((a : ℂ) * v - c * u - m * L.ω₂) = (a : ℂ) * (π * v) - c * (π * u) - m * (π * L.ω₂) := by
      ring
    rw [e2, f]
    exact sub_mem (sub_mem (int_mul_mem L a hv1) (int_mul_mem L c hu1))
      (int_mul_mem L m (hπL _ L.ω₂_mem_lattice))
  intro w hw
  obtain ⟨p, q, rfl⟩ := PeriodPair.mem_lattice.1 hw
  have f : π / 2 * ((p : ℂ) * L.ω₁ + q * L.ω₂) = (p : ℂ) * (π * (L.ω₁ / 2)) + q * (π * (L.ω₂ / 2)) := by
    ring
  rw [f]
  exact add_mem (int_mul_mem L p h1) (int_mul_mem L q h2)

def S (L : PeriodPair) (π : ℂ) (i : ℕ) : Submodule ℤ ℂ where
  carrier := {z | π * z ∈ L.lattice ∧ (2 : ℂ) ^ i * z ∈ L.lattice}
  add_mem' := by
    rintro a b ⟨h1, h2⟩ ⟨h3, h4⟩
    exact ⟨by rw [mul_add]; exact add_mem h1 h3, by rw [mul_add]; exact add_mem h2 h4⟩
  zero_mem' := by
    show π * 0 ∈ L.lattice ∧ (2 : ℂ) ^ i * 0 ∈ L.lattice
    simp
  smul_mem' := by
    rintro c z ⟨h1, h2⟩
    exact ⟨by rw [mul_smul_comm]; exact Submodule.smul_mem _ c h1,
      by rw [mul_smul_comm]; exact Submodule.smul_mem _ c h2⟩

theorem mem_S {L : PeriodPair} {π : ℂ} {i : ℕ} {z : ℂ} :
    z ∈ S L π i ↔ π * z ∈ L.lattice ∧ (2 : ℂ) ^ i * z ∈ L.lattice := Iff.rfl

end PI.GoodTwo.ChainBetweenPairs
