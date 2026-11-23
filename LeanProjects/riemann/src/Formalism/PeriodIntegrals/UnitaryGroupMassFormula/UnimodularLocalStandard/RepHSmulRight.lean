import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnimodularLocalStandard.RepPrimPair
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnimodularLocalStandard.RepRepModl
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnimodularLocalStandard.RepNewton
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnimodularLocalStandard.RepRamDef

noncomputable section
open scoped ComplexConjugate

namespace PI.UnitaryGroupMassFormula.UnimodLocStd
open PI.ULS

theorem rep_H_add_self (L : PeriodPair) (m : Type) [Fintype m] [DecidableEq m] (u v : m → ℂ) :
    stdH L m (u + v) (u + v) = stdH L m u u + stdH L m u v + stdH L m v u + stdH L m v v := by
  first
  | (simp only [map_add, LinearMap.add_apply]; ring)
  | (simp only [stdH, matH, LinearMap.mk₂'ₛₗ_apply, Pi.add_apply, map_add, add_mul, mul_add,
      Finset.sum_add_distrib]; ring)

theorem rep_H_smul_left (L : PeriodPair) (m : Type) [Fintype m] [DecidableEq m] (ξ : ℂ) (u v : m → ℂ) :
    stdH L m (ξ • u) v = ξ * stdH L m u v := by
  first
  | (simp only [map_smul, LinearMap.smul_apply, smul_eq_mul])
  | (simp only [stdH, matH, LinearMap.mk₂'ₛₗ_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc])

theorem rep_H_smul_right (L : PeriodPair) (m : Type) [Fintype m] [DecidableEq m] (ξ : ℂ) (u v : m → ℂ) :
    stdH L m v (ξ • u) = conj ξ * stdH L m v u := by
  first
  | (simp only [LinearMap.map_smulₛₗ, smul_eq_mul])
  | (simp only [stdH, matH, LinearMap.mk₂'ₛₗ_apply, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum];
     refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_; ring)

theorem rep_unit_vec (a : ℕ) (b c : ℤ) (d : ℕ) (ha : 0 < a) (hd : 0 < d) (lam : ℂ) (hlam : lam ≠ 0) (m : Type) [Fintype m] [DecidableEq m] (Λ : AddSubgroup (m → ℂ)) (l : ℕ) (x y : ℤ) (T : Finset m) (i₀ : m) (h : KeyHyps a b c d ha hd lam hlam m Λ l x y T i₀) (hld : ¬ (l : ℤ) ∣ d) :
    ∃ w : m → ℂ, SatMem l Λ w ∧ (∀ j ∈ T, w j = 0) ∧ ∃ N S : ℤ, ¬ (l : ℤ) ∣ N ∧ ¬ (l : ℤ) ∣ S ∧
      stdH (cmL a b d ha hd lam hlam) m w w = repKappa a b d ha hd lam hlam * ((N : ℂ) / S) := by
  obtain ⟨xt, hxt, hxtT, yv, hyv, c₂, hc₂, hc₂l⟩ := rep_prim_pair a b c d ha hd lam hlam m Λ l x y T i₀ h
  obtain ⟨hOK, hΛ, hθ, h1, h2, hl, hQ, hi₀, hT⟩ := h
  set L := cmL a b d ha hd lam hlam with hL
  set H := stdH L m with hHdef
  obtain ⟨κ, hκdef⟩ : ∃ κ, κ = repKappa a b d ha hd lam hlam := ⟨_, rfl⟩
  rw [← hκdef]
  set θ := cmTheta b d with hθdef
  have hlp : Prime (l : ℤ) := Nat.prime_iff_prime_int.mp hl
  obtain ⟨mm, c₂', hmc, hc₂'⟩ := rep_H_int a b c d ha hd lam hlam m hOK Λ hΛ hθ hxt hyv
  rw [← hκdef] at hmc
  have hcc : c₂' = c₂ := by
    have : (c₂' : ℝ) = c₂ := by rw [← hc₂', hc₂]
    exact_mod_cast this
  rw [hcc] at hmc
  obtain ⟨m1, hm1⟩ := rep_H_self_int a b c d ha hd lam hlam m hOK Λ hΛ hθ hxt
  rw [← hκdef] at hm1
  have hy'sat := rep_zT_sat a b c d ha hd lam hlam m hOK Λ hΛ hθ hl x y hQ T hT hyv
  set yz := zT T yv with hyz
  have hyzT : ∀ j ∈ T, yz j = 0 := by intro j hj; simp [hyz, zT, hj]
  obtain ⟨n', hn', hn'y⟩ := hy'sat
  obtain ⟨m2, hm2⟩ := rep_H_self_int a b c d ha hd lam hlam m hOK Λ hΛ hθ hn'y
  rw [rep_H_nsmul, ← hκdef] at hm2
  have hn'0 : (n' : ℂ) ≠ 0 := by
    have : n' ≠ 0 := by rintro rfl; exact hn' (dvd_zero _)
    exact_mod_cast this
  have hS : ¬ (l : ℤ) ∣ (n' : ℤ) ^ 2 := fun h => hn' (by exact_mod_cast hlp.dvd_of_dvd_pow h)
  have hyy : H yz yz = κ * ((m2 : ℂ) / ((n' : ℤ) ^ 2 : ℤ)) := by
    push_cast; field_simp; linear_combination hm2
  have hκc : conj κ = κ := by
    rw [hκdef, rep_kappa_eq a b d ha hd lam hlam, map_div₀, Complex.conj_ofReal, map_ofNat]
  have hxy : H xt yz = κ * ((mm : ℂ) - c₂ * conj θ) := by rw [hHdef, rep_H_zT a b d ha hd lam hlam m T hxtT]; exact hmc
  have hyx : H yz xt = κ * ((mm : ℂ) - c₂ * θ) := by
    rw [hHdef, ← rep_H_conj, ← hHdef, hxy, map_mul, hκc, map_sub, map_mul, map_intCast, map_intCast,
      Complex.conj_conj]
  have e1 := rep_theta_add_conj b d
  have e2 := rep_theta_mul_conj a b c d hOK.1

  by_cases k1 : (l : ℤ) ∣ m1
  swap
  · refine ⟨xt, rep_sat_of_mem l Λ hxt hl, hxtT, m1 * n' ^ 2, n' ^ 2, ?_, hS, ?_⟩
    · intro hh; rcases hlp.dvd_mul.mp hh with hh | hh
      · exact k1 hh
      · exact hS hh
    · rw [hm1]; push_cast; field_simp
  by_cases k2 : (l : ℤ) ∣ m2
  swap
  · exact ⟨yz, ⟨n', hn', hn'y⟩, hyzT, m2, n' ^ 2, k2, hS, hyy⟩
  by_cases k3 : (l : ℤ) ∣ (m1 + 2 * mm - c₂ * b) * n' ^ 2 + m2
  swap
  · refine ⟨xt + yz, rep_sat_add l Λ hl (rep_sat_of_mem l Λ hxt hl) ⟨n', hn', hn'y⟩, ?_, _, n' ^ 2, k3, hS, ?_⟩
    · intro j hj; simp [hxtT j hj, hyzT j hj]
    · rw [rep_H_add_self, hm1, hxy, hyx, hyy]
      push_cast; field_simp
      linear_combination (-κ * c₂ * (n' : ℂ) ^ 2) * e1
  by_cases k4 : (l : ℤ) ∣ (a * c * m1 + mm * b - 2 * a * c * c₂) * n' ^ 2 + m2
  swap
  · refine ⟨θ • xt + yz, rep_sat_add l Λ hl (rep_sat_theta l Λ hθ (rep_sat_of_mem l Λ hxt hl)) ⟨n', hn', hn'y⟩,
      ?_, _, n' ^ 2, k4, hS, ?_⟩
    · intro j hj; simp [hxtT j hj, hyzT j hj]
    · rw [rep_H_add_self, rep_H_smul, rep_H_smul_left, rep_H_smul_right, hm1, hxy, hyx, hyy]
      push_cast; field_simp
      linear_combination (κ * (n' : ℂ) ^ 2 * m1) * e2 + (κ * (n' : ℂ) ^ 2 * mm) * e1 -
        (2 * κ * (n' : ℂ) ^ 2 * c₂) * e2
  exfalso
  have d3 : (l : ℤ) ∣ (2 * mm - c₂ * b) * n' ^ 2 := by
    have e : (2 * mm - c₂ * b) * (n' : ℤ) ^ 2 = ((m1 + 2 * mm - c₂ * b) * n' ^ 2 + m2) - m1 * n' ^ 2 - m2 := by ring
    rw [e]; exact dvd_sub (dvd_sub k3 (Dvd.dvd.mul_right k1 _)) k2
  have d4 : (l : ℤ) ∣ (mm * b - 2 * a * c * c₂) * n' ^ 2 := by
    have e : (mm * b - 2 * a * c * c₂) * (n' : ℤ) ^ 2 =
        ((a * c * m1 + mm * b - 2 * a * c * c₂) * n' ^ 2 + m2) - (a * c) * m1 * n' ^ 2 - m2 := by ring
    rw [e]; exact dvd_sub (dvd_sub k4 (Dvd.dvd.mul_right (Dvd.dvd.mul_left k1 _) _)) k2
  have d3' : (l : ℤ) ∣ 2 * mm - c₂ * b := (hlp.dvd_mul.mp d3).resolve_right hS
  have d4' : (l : ℤ) ∣ mm * b - 2 * a * c * c₂ := (hlp.dvd_mul.mp d4).resolve_right hS
  have d5 : (l : ℤ) ∣ c₂ * d := by
    have e : c₂ * (d : ℤ) = b * (2 * mm - c₂ * b) - 2 * (mm * b - 2 * a * c * c₂) := by
      linear_combination (-c₂) * hOK.1
    rw [e]; exact dvd_sub (Dvd.dvd.mul_left d3' b) (Dvd.dvd.mul_left d4' 2)
  rcases hlp.dvd_mul.mp d5 with h5 | h5
  · exact hc₂l h5
  · exact hld h5

theorem keyStart_of_ram (hR : KeyStartRam) : KeyStart := by
  intro a b c d ha hd lam hlam m _ _ Λ l x y T i₀ h
  by_cases hld : l = d
  · exact hR a b c d ha hd lam hlam m Λ l x y T i₀ h hld
  have hOK := h.1
  have hl := h.2.2.2.2.2.1
  have hQ := h.2.2.2.2.2.2.1
  have hθ := h.2.2.1
  have hld' : ¬ (l : ℤ) ∣ d := by
    intro hh
    have : l ∣ d := by exact_mod_cast hh
    exact hld ((Nat.prime_dvd_prime_iff_eq hl hOK.2.2.2).mp this)
  obtain ⟨w, hw, hwT, N, S, hN, hS, hH⟩ := rep_unit_vec a b c d ha hd lam hlam m Λ l x y T i₀ h hld'
  obtain ⟨s, t, p, hp⟩ := rep_rep_modl hl a b c d hOK.1 hld' N S _ hN hS hQ
  have hlp : Prime (l : ℤ) := Nat.prime_iff_prime_int.mp hl
  refine ⟨((s : ℂ) + t * cmTheta b d) • w, ?_, ?_, p, (a * x ^ 2 + b * x * y + c * y ^ 2) * S, ?_, ?_⟩
  · rw [add_smul, ← smul_smul]
    exact rep_sat_add l Λ hl (rep_sat_zsmul l Λ hw s) (rep_sat_zsmul l Λ (rep_sat_theta l Λ hθ hw) t)
  · intro j hj; simp [hwT j hj]
  · intro hh; rcases hlp.dvd_mul.mp hh with hh | hh
    · exact hQ hh
    · exact hS hh
  · have hS0 : (S : ℂ) ≠ 0 := by
      have : S ≠ 0 := by rintro rfl; exact hS (dvd_zero _)
      exact_mod_cast this
    obtain ⟨Q0, hQ0def⟩ : ∃ Q0 : ℤ, Q0 = a * x ^ 2 + b * x * y + c * y ^ 2 := ⟨_, rfl⟩
    rw [← hQ0def] at hp hQ ⊢
    have hQ0 : (Q0 : ℂ) ≠ 0 := by
      have : Q0 ≠ 0 := by rintro rfl; exact hQ (dvd_zero _)
      exact_mod_cast this
    have hf' : stdH (cmL a b d ha hd lam hlam) m (fvec a b d lam x y i₀) (fvec a b d lam x y i₀) =
        repKappa a b d ha hd lam hlam * (Q0 : ℂ) := by
      rw [rep_norm_f a b c d ha hd lam hlam m hOK.1 x y i₀, hQ0def]
    have e1 := rep_theta_add_conj b d
    have e2 := rep_theta_mul_conj a b c d hOK.1
    have hX : ((s : ℂ) + t * cmTheta b d) * conj ((s : ℂ) + t * cmTheta b d) =
        ((s ^ 2 + b * s * t + a * c * t ^ 2 : ℤ) : ℂ) := by
      simp only [map_add, map_mul, map_intCast]; push_cast
      linear_combination ((s : ℂ) * t) * e1 + (t : ℂ) ^ 2 * e2
    have hpC : (l : ℂ) ^ 1 * (p : ℂ) = ((s ^ 2 + b * s * t + a * c * t ^ 2 : ℤ) : ℂ) * N - (Q0 : ℂ) * S := by
      rw [pow_one]; exact_mod_cast hp.symm
    rw [rep_H_smul, hX, hH, hf', hpC]
    push_cast
    field_simp
    ring

end PI.UnitaryGroupMassFormula.UnimodLocStd
