import Mathlib
import GroundTheory.LocalFields.UnitsPowers
import GroundTheory.LocalFields.NormalLattice
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open GroundTheory.LocalField ValuativeRel IsLocalRing Polynomial

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

theorem one_add_pow_prime_eq {p : ℕ} (hp : p.Prime) {z : 𝒪[K]} (hz : z ∈ 𝓂[K]) :
    ∃ y ∈ 𝓂[K], (1 + z) ^ p = 1 + z ^ p + p * z * (1 + y) := by
  rw [add_comm (1 : 𝒪[K]) z, add_pow_prime_eq hp z 1]
  set r := ∑ k ∈ Finset.Ioo 0 p, z ^ (k - 1) * 1 ^ (p - k - 1) * ((p.choose k / p : ℕ) : 𝒪[K])
  refine ⟨r - 1, ?_, by ring⟩
  rw [← residue_eq_zero_iff, map_sub, map_one, sub_eq_zero]
  have hz' : residue 𝒪[K] z = 0 := (residue_eq_zero_iff _).mpr hz
  simp only [r, map_sum, map_mul, map_pow, hz', one_pow, map_natCast, mul_one]
  rw [Finset.sum_eq_single 1]
  · simp [Nat.div_self hp.pos]
  · intro k hk hk1
    have : k - 1 ≠ 0 := by simp at hk; omega
    simp [zero_pow this]
  · intro h
    exact absurd (by simp; exact hp.one_lt) h

theorem exists_pow_eq_of_mem_unitFiltration_one {m : ℕ} (hm : (m : 𝓀[K]) ≠ 0) {w : 𝒪[K]ˣ}
    (hw : w ∈ unitFiltration K 1) : ∃ u ∈ unitFiltration K 1, u ^ m = w := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  have hu : IsUnit (m : 𝒪[K]) := by
    rw [← residue_ne_zero_iff_isUnit, map_natCast]; exact hm
  have hm0 : m ≠ 0 := by rintro rfl; simp at hm
  set f : 𝒪[K][X] := X ^ m - C (w : 𝒪[K])
  obtain ⟨b, hb, hb1⟩ := exists_root_of_dvd hϖ f 1 0 hu.unit
    (by simp [f, derivative_X_pow])
    (by
      have := (mem_maximalIdeal_pow_iff hϖ).mp (mem_unitFiltration.mp hw)
      have e' : f.eval 1 = -((w : 𝒪[K]) - 1) := by simp [f]
      rw [e', dvd_neg]
      simpa using this)
  have hbm : b ^ m = w := by simpa [f, sub_eq_zero] using hb
  have hbu : IsUnit b := (isUnit_pow_iff hm0).mp (hbm ▸ w.isUnit)
  refine ⟨hbu.unit, ?_, by ext; simp [hbm]⟩
  rw [mem_unitFiltration, mem_maximalIdeal_pow_iff hϖ]
  simpa using hb1

variable {ϖ : 𝒪[K]} (hϖ : Irreducible ϖ) {p : ℕ} (hp : p.Prime) {e : ℕ} {ε : 𝒪[K]ˣ}
  (hpe : (p : 𝒪[K]) = ϖ ^ e * ε)
include hϖ hp hpe

theorem one_add_pow_sub_one_eq {j : ℕ} (hj : e + 1 ≤ j) (x : 𝒪[K]) :
    ∃ w : 𝒪[K], (1 + ϖ ^ j * x) ^ p - 1 = ϖ ^ (j + e) * (ε * x + ϖ * w) := by
  have hj1 : 1 ≤ j := by omega
  obtain ⟨y, hy, h⟩ := one_add_pow_prime_eq hp (z := ϖ ^ j * x)
    (Ideal.mul_mem_right _ _ (Ideal.pow_mem_of_mem _ (uniformizer_mem_maximalIdeal hϖ) j hj1))
  obtain ⟨t, rfl⟩ := (mem_maximalIdeal_iff_dvd hϖ).mp hy
  have h2 : 2 * j ≤ p * j := Nat.mul_le_mul_right j hp.two_le
  obtain ⟨m, hm⟩ : ∃ m, p * j = j + e + 1 + m := ⟨p * j - (j + e + 1), by omega⟩
  refine ⟨ϖ ^ m * x ^ p + ε * x * t, ?_⟩
  have hpow : (ϖ ^ j * x) ^ p = ϖ ^ (j + e + 1 + m) * x ^ p := by
    rw [mul_pow, ← pow_mul, mul_comm j p, hm]
  rw [h, hpow, hpe]
  ring

theorem pow_mem_unitFiltration {j : ℕ} (hj : e + 1 ≤ j) {u : 𝒪[K]ˣ}
    (hu : u ∈ unitFiltration K j) : u ^ p ∈ unitFiltration K (j + e) := by
  obtain ⟨a, ha⟩ := exists_sub_one_eq_mul hϖ ⟨u, hu⟩
  obtain ⟨w, hw⟩ := one_add_pow_sub_one_eq hϖ hp hpe hj a
  rw [mem_unitFiltration, mem_maximalIdeal_pow_iff hϖ, Units.val_pow_eq_pow_val,
    show (u : 𝒪[K]) = 1 + ϖ ^ j * a by simp only at ha; rw [← ha]; ring, hw]
  exact dvd_mul_right _ _

theorem pow_mem_unitFiltration_succ_iff {j : ℕ} (hj : e + 1 ≤ j) {u : 𝒪[K]ˣ}
    (hu : u ∈ unitFiltration K j) :
    u ^ p ∈ unitFiltration K (j + e + 1) ↔ u ∈ unitFiltration K (j + 1) := by
  obtain ⟨a, ha⟩ := exists_sub_one_eq_mul hϖ ⟨u, hu⟩
  obtain ⟨w, hw⟩ := one_add_pow_sub_one_eq hϖ hp hpe hj a
  have hu' : (u : 𝒪[K]) = 1 + ϖ ^ j * a := by simp only at ha; rw [← ha]; ring
  rw [mem_unitFiltration, mem_maximalIdeal_pow_iff hϖ, Units.val_pow_eq_pow_val, hu', hw,
    mem_unitFiltration, mem_maximalIdeal_pow_iff hϖ, hu', add_sub_cancel_left, pow_succ,
    pow_succ, mul_dvd_mul_iff_left (pow_ne_zero _ hϖ.ne_zero),
    mul_dvd_mul_iff_left (pow_ne_zero _ hϖ.ne_zero), dvd_add_left (dvd_mul_right ϖ w),
    Units.dvd_mul_left]

theorem eq_one_of_mem_unitFiltration_of_pow_eq_one {k : ℕ} (hk : e + 1 ≤ k) {u : 𝒪[K]ˣ}
    (hu : u ∈ unitFiltration K k) (h : u ^ p = 1) : u = 1 := by
  have hall : ∀ n, u ∈ unitFiltration K (k + n) := by
    intro n
    induction n with
    | zero => simpa using hu
    | succ n ih =>
      have := (pow_mem_unitFiltration_succ_iff hϖ hp hpe (by omega) ih).mp
        (by rw [h]; exact one_mem _)
      simpa [add_assoc] using this
  have h0 : (u : 𝒪[K]) - 1 = 0 := by
    refine eq_zero_of_forall_pow_dvd hϖ fun N => ?_
    have := unitFiltration_antitone K (Nat.le_add_left N k) (hall N)
    exact (mem_maximalIdeal_pow_iff hϖ).mp (mem_unitFiltration.mp this)
  ext
  simpa [sub_eq_zero] using h0

theorem exists_pow_eq_of_mem_unitFiltration {k : ℕ} (hk : e + 1 ≤ k) {w : 𝒪[K]ˣ}
    (hw : w ∈ unitFiltration K (k + e)) : ∃ u ∈ unitFiltration K k, u ^ p = w := by
  set f : 𝒪[K][X] := X ^ p - C (w : 𝒪[K])
  obtain ⟨b, hb, hb1⟩ := exists_root_of_dvd hϖ f 1 e ε
    (by
      simp only [f, derivative_sub, derivative_C, sub_zero, derivative_X_pow, eval_mul,
        eval_C, eval_pow, eval_X, one_pow, mul_one]
      exact hpe)
    (by
      have hw' := unitFiltration_antitone K (show 2 * e + 1 ≤ k + e by omega) hw
      have := (mem_maximalIdeal_pow_iff hϖ).mp (mem_unitFiltration.mp hw')
      have e' : f.eval 1 = -((w : 𝒪[K]) - 1) := by simp [f]
      rw [e', dvd_neg]
      exact this)
  have hbp : b ^ p = w := by simpa [f, sub_eq_zero] using hb
  have hbu : IsUnit b := (isUnit_pow_iff hp.ne_zero).mp (hbp ▸ w.isUnit)
  set u := hbu.unit
  have hup : u ^ p = w := by ext; simp [u, hbp]
  refine ⟨u, ?_, hup⟩
  have hstep : ∀ i, e + 1 + i ≤ k → u ∈ unitFiltration K (e + 1 + i) := by
    intro i
    induction i with
    | zero =>
      intro _
      rw [mem_unitFiltration, mem_maximalIdeal_pow_iff hϖ]
      simpa [u] using hb1
    | succ i ih =>
      intro hi
      have hmem := ih (by omega)
      have := (pow_mem_unitFiltration_succ_iff hϖ hp hpe (by omega) hmem).mp
        (by rw [hup]; exact unitFiltration_antitone K (by omega) hw)
      simpa [add_assoc] using this
  simpa [show e + 1 + (k - (e + 1)) = k by omega] using hstep (k - (e + 1)) (by omega)

end GroundTheory.ProfCoh
