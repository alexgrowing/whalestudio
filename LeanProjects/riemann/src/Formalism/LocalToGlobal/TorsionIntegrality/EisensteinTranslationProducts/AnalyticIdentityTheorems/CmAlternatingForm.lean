import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.CMQuasiPeriodConst

noncomputable section
open scoped BigOperators ComplexConjugate

namespace Formalism.L2.Th1.F

namespace Cm1

private theorem cmTheta_eq_half_b_add_sqrt_half_I (b : ℤ) (d : ℕ) :
    Formalism.L2.Th1.F.cmTheta b d = (((b : ℝ) / 2 : ℝ) : ℂ) + ((Real.sqrt d / 2 : ℝ) : ℂ) * Complex.I := by
  unfold Formalism.L2.Th1.F.cmTheta; push_cast; ring

private theorem re_ofReal_add_ofReal_mul_I (u v : ℝ) : ((u : ℂ) + (v : ℂ) * Complex.I).re = u := by simp

lemma theta_re (b : ℤ) (d : ℕ) : (cmTheta b d).re = (b : ℝ) / 2 := by
  rw [cmTheta_eq_half_b_add_sqrt_half_I, re_ofReal_add_ofReal_mul_I]

private theorem im_ofReal_add_ofReal_mul_I (u v : ℝ) : ((u : ℂ) + (v : ℂ) * Complex.I).im = v := by simp

lemma theta_im (b : ℤ) (d : ℕ) : (cmTheta b d).im = Real.sqrt d / 2 := by
  rw [cmTheta_eq_half_b_add_sqrt_half_I, im_ofReal_add_ofReal_mul_I]

lemma sqrt_mul_self (d : ℕ) : Real.sqrt d * Real.sqrt d = d :=
  Real.mul_self_sqrt (Nat.cast_nonneg d)

lemma sqrt_mul_selfC (d : ℕ) : ((Real.sqrt d : ℝ) : ℂ) * ((Real.sqrt d : ℝ) : ℂ) = (d : ℂ) := by
  rw [← Complex.ofReal_mul, sqrt_mul_self, Complex.ofReal_natCast]

lemma sqrt_pos' (d : ℕ) (hd : 0 < d) : 0 < Real.sqrt d :=
  Real.sqrt_pos.mpr (by exact_mod_cast hd)

lemma conj_theta (b : ℤ) (d : ℕ) :
    conj (cmTheta b d) = ((b : ℂ) - Complex.I * ((Real.sqrt d : ℝ) : ℂ)) / 2 := by
  rw [cmTheta_eq_half_b_add_sqrt_half_I]
  simp only [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

private theorem four_mul_a_mul_c_complex_of_int (a : ℕ) (b c : ℤ) (d : ℕ) (h : 4 * (a : ℤ) * c = b ^ 2 + d) :
    (4 : ℂ) * (a : ℂ) * (c : ℂ) = (b : ℂ) ^ 2 + (d : ℂ) := by
  have h' := congrArg (fun t : ℤ => (t : ℂ)) h
  push_cast at h'
  linear_combination h'

lemma theta_sq (a : ℕ) (b c : ℤ) (d : ℕ) (h : 4 * (a : ℤ) * c = b ^ 2 + d) :
    cmTheta b d ^ 2 = (b : ℂ) * cmTheta b d - (a : ℂ) * (c : ℂ) := by
  have hs := sqrt_mul_selfC d
  have hc := four_mul_a_mul_c_complex_of_int a b c d h
  unfold Formalism.L2.Th1.F.cmTheta
  linear_combination ((1 / 4 : ℂ) * ((Real.sqrt d : ℝ) : ℂ) ^ 2) * Complex.I_sq
    - (1 / 4 : ℂ) * hs + (1 / 4 : ℂ) * hc

lemma coord (a : ℕ) (b : ℤ) (d : ℕ) (ha : 0 < a) (hd : 0 < d) (x y : ℝ)
    (h : (x : ℂ) * (a : ℂ) + (y : ℂ) * cmTheta b d = 0) : x = 0 ∧ y = 0 := by
  have hs := sqrt_pos' d hd
  have ha' : (0 : ℝ) < a := by exact_mod_cast ha
  have h1 : ((x * a + y * (b / 2) : ℝ) : ℂ) + ((y * (Real.sqrt d / 2) : ℝ) : ℂ) * Complex.I = 0 := by
    rw [cmTheta_eq_half_b_add_sqrt_half_I] at h
    push_cast at h ⊢
    linear_combination h
  have hre : x * a + y * (b / 2) = 0 := by
    have h2 := congrArg Complex.re h1
    rwa [re_ofReal_add_ofReal_mul_I, Complex.zero_re] at h2
  have him : y * (Real.sqrt d / 2) = 0 := by
    have h2 := congrArg Complex.im h1
    rwa [im_ofReal_add_ofReal_mul_I, Complex.zero_im] at h2
  have hy : y = 0 := by
    rcases mul_eq_zero.mp him with h' | h'
    · exact h'
    · linarith
  subst hy
  refine ⟨?_, rfl⟩
  have hxa : x * a = 0 := by linarith
  rcases mul_eq_zero.mp hxa with h' | h'
  · exact h'
  · linarith

lemma mem_iff (a : ℕ) (b : ℤ) (d : ℕ) (ha : 0 < a) (hd : 0 < d) (z : ℂ) :
    z ∈ (cmPair a b d ha hd).lattice ↔ ∃ x y : ℤ, (x : ℂ) * (a : ℂ) + (y : ℂ) * cmTheta b d = z := by
  exact PeriodPair.mem_lattice

end Cm1

open Cm1

theorem cm_theta_eq : CmThetaEq := by
  intro a b c d h
  have hs := Formalism.L2.Th1.F.Cm1.sqrt_mul_selfC d
  have hc := _root_.Formalism.L2.Th1.F.Cm1.four_mul_a_mul_c_complex_of_int a b c d h
  refine ⟨Formalism.L2.Th1.F.Cm1.theta_sq a b c d h, ?_, ?_⟩
  · rw [Formalism.L2.Th1.F.Cm1.conj_theta]; unfold cmTheta; ring
  · rw [Formalism.L2.Th1.F.Cm1.conj_theta]; unfold cmTheta
    linear_combination (-(1 / 4 : ℂ) * ((Real.sqrt d : ℝ) : ℂ) ^ 2) * Complex.I_sq
      + (1 / 4 : ℂ) * hs - (1 / 4 : ℂ) * hc

theorem cm_stable : CmStable := by
  intro a b c d ha hd h m n z hz
  have hsq := Formalism.L2.Th1.F.Cm1.theta_sq a b c d h
  obtain ⟨x, y, rfl⟩ := (Formalism.L2.Th1.F.Cm1.mem_iff a b d ha hd z).mp hz
  refine (Formalism.L2.Th1.F.Cm1.mem_iff a b d ha hd _).mpr ⟨m * x - n * y * c, m * y + n * x * a + n * y * b, ?_⟩
  push_cast
  linear_combination (-((n : ℂ) * (y : ℂ))) * hsq

theorem cm_order : CmOrder := by
  intro a b c d ha hd h hg α hα
  have hsq := Formalism.L2.Th1.F.Cm1.theta_sq a b c d h
  have ha0 : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  have haL : (a : ℂ) ∈ (cmPair a b d ha hd).lattice :=
    (Formalism.L2.Th1.F.Cm1.mem_iff a b d ha hd _).mpr ⟨1, 0, by simp⟩
  have hωL : cmTheta b d ∈ (cmPair a b d ha hd).lattice :=
    (Formalism.L2.Th1.F.Cm1.mem_iff a b d ha hd _).mpr ⟨0, 1, by simp⟩
  obtain ⟨x, y, eq1⟩ := (Formalism.L2.Th1.F.Cm1.mem_iff a b d ha hd _).mp (hα _ haL)
  obtain ⟨u, v, eq2⟩ := (Formalism.L2.Th1.F.Cm1.mem_iff a b d ha hd _).mp (hα _ hωL)
  obtain ⟨k1, k2⟩ := Formalism.L2.Th1.F.Cm1.coord a b d ha hd ((u * a + y * c : ℤ) : ℝ)
    ((v * a - x * a - y * b : ℤ) : ℝ)
    (by push_cast; linear_combination (a : ℂ) * eq2 - cmTheta b d * eq1 + (y : ℂ) * hsq)
  have e1 : u * (a : ℤ) + y * c = 0 := by exact_mod_cast k1
  have e2 : v * (a : ℤ) - x * a - y * b = 0 := by exact_mod_cast k2
  have hb : y * b = a * (v - x) := by linear_combination -e2
  have hc : y * c = -(a * u) := by linear_combination e1
  obtain ⟨A, B, g1⟩ : ∃ A B : ℤ, ((Int.gcd (a : ℤ) b : ℕ) : ℤ) * A + c * B = 1 :=
    ⟨Int.gcdA ((Int.gcd (a : ℤ) b : ℕ) : ℤ) c, Int.gcdB ((Int.gcd (a : ℤ) b : ℕ) : ℤ) c, by
      rw [← Int.gcd_eq_gcd_ab, hg, Nat.cast_one]⟩
  obtain ⟨A', B', g2⟩ : ∃ A B : ℤ, (a : ℤ) * A + b * B = ((Int.gcd (a : ℤ) b : ℕ) : ℤ) :=
    ⟨_, _, (Int.gcd_eq_gcd_ab _ _).symm⟩
  have hy : y = a * (y * A' * A + (v - x) * B' * A - u * B) := by
    linear_combination -y * g1 - y * A * g2 + B' * A * hb + B * hc
  refine ⟨x, y * A' * A + (v - x) * B' * A - u * B, ?_⟩
  have hyC : (y : ℂ) = (a : ℂ) * ((y * A' * A + (v - x) * B' * A - u * B : ℤ) : ℂ) := by
    exact_mod_cast hy
  apply mul_right_cancel₀ ha0
  linear_combination -eq1 + cmTheta b d * hyC

private theorem area_cmPair (a : ℕ) (b : ℤ) (d : ℕ) (ha : 0 < a) (hd : 0 < d) :
    area (cmPair a b d ha hd) = (a : ℝ) * Real.sqrt d / 2 := by
  have key : conj (a : ℂ) * cmTheta b d
      = (((a : ℝ) * b / 2 : ℝ) : ℂ) + (((a : ℝ) * Real.sqrt d / 2 : ℝ) : ℂ) * Complex.I := by
    rw [map_natCast, _root_.Formalism.L2.Th1.F.Cm1.cmTheta_eq_half_b_add_sqrt_half_I]; push_cast; ring
  unfold area
  show |(conj (a : ℂ) * cmTheta b d).im| = _
  rw [key, _root_.Formalism.L2.Th1.F.Cm1.im_ofReal_add_ofReal_mul_I]
  exact abs_of_nonneg (by positivity)

theorem cm_area : CmArea := by
  intro a b d ha hd
  exact area_cmPair a b d ha hd

private theorem ofReal_add_mul_I_mul_conj (u v u' v' : ℝ) :
    ((u : ℂ) + (v : ℂ) * Complex.I) * conj ((u' : ℂ) + (v' : ℂ) * Complex.I)
      = ((u * u' + v * v' : ℝ) : ℂ) + ((v * u' - u * v' : ℝ) : ℂ) * Complex.I := by
  simp only [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  linear_combination (-((v : ℂ) * (v' : ℂ))) * Complex.I_sq

private theorem ofReal_add_mul_I_div_ofReal (u v r : ℝ) :
    ((u : ℂ) + (v : ℂ) * Complex.I) / (r : ℂ) = ((u / r : ℝ) : ℂ) + ((v / r : ℝ) : ℂ) * Complex.I := by
  push_cast; ring

private theorem intCast_mul_add_mul_cmTheta_eq (a : ℕ) (b : ℤ) (d : ℕ) (m n : ℤ) :
    (m : ℂ) * (a : ℂ) + (n : ℂ) * cmTheta b d
      = (((m : ℝ) * a + n * b / 2 : ℝ) : ℂ) + (((n : ℝ) * Real.sqrt d / 2 : ℝ) : ℂ) * Complex.I := by
  rw [_root_.Formalism.L2.Th1.F.Cm1.cmTheta_eq_half_b_add_sqrt_half_I]; push_cast; ring

private theorem four_mul_a_mul_c_real_of_int (a : ℕ) (b c : ℤ) (d : ℕ) (h : 4 * (a : ℤ) * c = b ^ 2 + d) :
    (4 : ℝ) * (a : ℝ) * (c : ℝ) = (b : ℝ) ^ 2 + (d : ℝ) := by
  have h' := congrArg (fun t : ℤ => (t : ℝ)) h
  push_cast at h'
  linear_combination h'

private theorem normSq_coords_eq_a_mul_cmForm (a : ℕ) (b c : ℤ) (d : ℕ) (h : 4 * (a : ℤ) * c = b ^ 2 + d) (m n : ℤ) :
    ((m : ℝ) * a + n * b / 2) * ((m : ℝ) * a + n * b / 2)
      + ((n : ℝ) * Real.sqrt d / 2) * ((n : ℝ) * Real.sqrt d / 2)
      = (a : ℝ) * (cmForm a b c m n : ℝ) := by
  have hsd := Formalism.L2.Th1.F.Cm1.sqrt_mul_self d
  have hr := four_mul_a_mul_c_real_of_int a b c d h
  unfold cmForm
  push_cast
  linear_combination ((n : ℝ) ^ 2 / 4) * hsd - ((n : ℝ) ^ 2 / 4) * hr

theorem cm_norm : CmNorm := by
  intro a b c d ha hd h m n
  have hsd : Real.sqrt d ≠ 0 := (Formalism.L2.Th1.F.Cm1.sqrt_pos' d hd).ne'
  have hA : (a : ℝ) * Real.sqrt d / 2 ≠ 0 :=
    (div_pos (mul_pos (by exact_mod_cast ha) (Formalism.L2.Th1.F.Cm1.sqrt_pos' d hd)) two_pos).ne'
  have hN := normSq_coords_eq_a_mul_cmForm a b c d h m n
  have hnorm : Complex.normSq ((m : ℂ) * (a : ℂ) + (n : ℂ) * cmTheta b d)
      = (a : ℝ) * (cmForm a b c m n : ℝ) := by
    rw [intCast_mul_add_mul_cmTheta_eq, Complex.normSq_apply, _root_.Formalism.L2.Th1.F.Cm1.re_ofReal_add_ofReal_mul_I, _root_.Formalism.L2.Th1.F.Cm1.im_ofReal_add_ofReal_mul_I]; exact hN
  refine ⟨hnorm, ?_, ?_⟩
  · unfold herm
    rw [area_cmPair, intCast_mul_add_mul_cmTheta_eq, ofReal_add_mul_I_mul_conj, ofReal_add_mul_I_div_ofReal]
    apply Complex.ext
    · rw [_root_.Formalism.L2.Th1.F.Cm1.re_ofReal_add_ofReal_mul_I, Complex.ofReal_re, hN, div_eq_div_iff hA hsd]; ring
    · rw [_root_.Formalism.L2.Th1.F.Cm1.im_ofReal_add_ofReal_mul_I, Complex.ofReal_im]; ring
  · intro hmn
    have hz : (m : ℂ) * (a : ℂ) + (n : ℂ) * cmTheta b d ≠ 0 := by
      intro h0
      obtain ⟨h1, h2⟩ := Formalism.L2.Th1.F.Cm1.coord a b d ha hd (m : ℝ) (n : ℝ) (by exact_mod_cast h0)
      have hm : m = 0 := by exact_mod_cast h1
      have hn : n = 0 := by exact_mod_cast h2
      exact hmn (by rw [hm, hn])
    have hpos := Complex.normSq_pos.mpr hz
    rw [hnorm] at hpos
    have ha' : (0 : ℝ) < a := by exact_mod_cast ha
    have hQ : (0 : ℝ) < (cmForm a b c m n : ℝ) := by
      by_contra hneg
      have hneg' := not_lt.mp hneg
      nlinarith
    have hQ' : (0 : ℤ) < cmForm a b c m n := by exact_mod_cast hQ
    omega

theorem cm_alternating_form : CmAltE := by
  intro a b d ha hd m n m' n'
  have hA : (a : ℝ) * Real.sqrt d / 2 ≠ 0 :=
    (div_pos (mul_pos (by exact_mod_cast ha) (Formalism.L2.Th1.F.Cm1.sqrt_pos' d hd)) two_pos).ne'
  unfold altE herm
  rw [area_cmPair, intCast_mul_add_mul_cmTheta_eq a b d m n, intCast_mul_add_mul_cmTheta_eq a b d m' n', ofReal_add_mul_I_mul_conj, ofReal_add_mul_I_div_ofReal,
    _root_.Formalism.L2.Th1.F.Cm1.im_ofReal_add_ofReal_mul_I, div_eq_iff hA]
  push_cast
  ring

theorem cm_half_lattice_iff : CMHalfLatticeIff := by
  intro a b d ha hd hodd m n
  rw [Formalism.L2.Th1.F.Cm1.mem_iff a b d ha hd]
  constructor
  · rintro ⟨x, y, hxy⟩
    obtain ⟨h1, h2⟩ := Formalism.L2.Th1.F.Cm1.coord a b d ha hd ((x : ℝ) - (m : ℝ) / 2)
      ((y : ℝ) - (n : ℝ) * (a : ℝ) / 2) (by push_cast; linear_combination hxy)
    have hm : (m : ℝ) = 2 * x := by linarith
    have hm' : m = 2 * x := by exact_mod_cast hm
    have hn : (n : ℝ) * a = 2 * y := by linarith
    have hn' : n * (a : ℤ) = 2 * y := by exact_mod_cast hn
    obtain ⟨k, hk⟩ := hodd
    have hkZ : (a : ℤ) = 2 * k + 1 := by exact_mod_cast hk
    exact ⟨⟨x, by omega⟩, ⟨y - n * k, by linear_combination hn' - n * hkZ⟩⟩
  · rintro ⟨⟨r, rfl⟩, ⟨s, rfl⟩⟩
    exact ⟨r, s * a, by push_cast; ring⟩

end Formalism.L2.Th1.F
