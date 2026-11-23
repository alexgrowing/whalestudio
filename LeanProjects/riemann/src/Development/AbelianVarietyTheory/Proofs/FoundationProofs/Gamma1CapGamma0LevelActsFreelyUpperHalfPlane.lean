import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IsRootOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GlTwoPosRatMobiusBasicLaws
open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups

namespace GlobalTheory.KZ.FreeAct

theorem ent_ofSL (γ : SL(2, ℤ)) (i j : Fin 2) :
    ent (ofSL γ) i j = ((γ : Matrix (Fin 2) (Fin 2) ℤ) i j : ℚ) := by
  simp [ent, ofSL]

theorem key (a b c d x y : ℝ) (h1 : a - d = 2 * c * x) (h2 : c * (x ^ 2 - y ^ 2) + (d - a) * x - b = 0)
    (hdet : a * d - b * c = 1) : 4 * c ^ 2 * y ^ 2 = 4 - (a + d) ^ 2 := by
  linear_combination (-4 * c) * h2 + 4 * hdet + (a - d - 2 * c * x) * h1

theorem no_small (N : ℕ) (hN : 4 ≤ N) (t k : ℤ) (hk : t - 2 = (N : ℤ) * k) (ht : t ^ 2 < 4) : False := by
  have h1 : -1 ≤ t := by nlinarith
  have h2 : t ≤ 1 := by nlinarith
  have hN' : (4 : ℤ) ≤ N := by exact_mod_cast hN
  rcases lt_trichotomy k 0 with hk0 | hk0 | hk0
  · nlinarith
  · subst hk0; omega
  · nlinarith

end GlobalTheory.KZ.FreeAct

namespace GlobalTheory.KZ

open FreeAct in

theorem gam_free : ∀ (N l : ℕ), 4 ≤ N → ∀ γ ∈ Gam N l, ∀ z ∈ Hs, mob (ofSL γ) z = z → γ = 1 := by
  intro N l hN γ hγ z hz hfix
  have hγ1 : γ ∈ CongruenceSubgroup.Gamma1 N := hγ.1
  rw [CongruenceSubgroup.Gamma1_mem] at hγ1
  obtain ⟨ha1, hd1, -⟩ := hγ1
  set A := (γ : Matrix (Fin 2) (Fin 2) ℤ) with hA
  have hdet : A 0 0 * A 1 1 - A 0 1 * A 1 0 = 1 := by
    have := γ.2; rw [Matrix.det_fin_two] at this; exact this
  have hden := GlobalTheory.KZ.MobLaws.den_ne (ofSL γ) hz
  simp only [ent_ofSL] at hden
  unfold mob at hfix
  simp only [ent_ofSL] at hfix
  rw [div_eq_iff hden] at hfix
  have hy : 0 < z.im := hz
  have hre := congrArg Complex.re hfix
  have him := congrArg Complex.im hfix
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.intCast_re,
    Complex.intCast_im, Complex.ratCast_re, Complex.ratCast_im] at hre him
  push_cast at hre him
  simp at hre him
  obtain ⟨k, hk⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub 1 (A 0 0) N).1 (by simpa using ha1.symm)
  obtain ⟨m, hm⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub 1 (A 1 1) N).1 (by simpa using hd1.symm)
  have hN' : (4 : ℤ) ≤ N := by exact_mod_cast hN
  simp only [← hA] at hre him
  generalize e00 : A 0 0 = a at *
  generalize e01 : A 0 1 = b at *
  generalize e10 : A 1 0 = c at *
  generalize e11 : A 1 1 = d at *
  have h1 : (a : ℝ) - d = 2 * c * z.re := by
    have : ((a : ℝ) - d - 2 * c * z.re) * z.im = 0 := by linarith
    rcases mul_eq_zero.1 this with h | h
    · linarith
    · linarith
  have h2 : (c : ℝ) * (z.re ^ 2 - z.im ^ 2) + (d - a) * z.re - b = 0 := by linarith
  have hdetR : (a : ℝ) * d - b * c = 1 := by exact_mod_cast hdet
  have hk4 := key a b c d z.re z.im h1 h2 hdetR
  by_cases hc : c = 0
  · subst hc
    have had : a = d := by
      have : (a : ℝ) = d := by simp at h1; linarith
      exact_mod_cast this
    subst had
    have hb : b = 0 := by
      have : (b : ℝ) = 0 := by simpa using h2
      exact_mod_cast this
    subst hb
    have haa : a * a = 1 := by simpa using hdet
    rcases Int.eq_one_or_neg_one_of_mul_eq_one' haa with ⟨ha, -⟩ | ⟨ha, -⟩
    · subst ha
      ext i j
      fin_cases i <;> fin_cases j <;> simp [← hA, e00, e01, e10, e11]
    · exfalso
      subst ha
      rcases lt_trichotomy k 0 with hk0 | hk0 | hk0
      · nlinarith
      · subst hk0; omega
      · nlinarith
  · exfalso
    have hcR : (c : ℝ) ≠ 0 := by exact_mod_cast hc
    have hpos : 0 < 4 * (c : ℝ) ^ 2 * z.im ^ 2 := by positivity
    have ht : (a + d) ^ 2 < 4 := by
      have : ((a : ℝ) + d) ^ 2 < 4 := by linarith
      exact_mod_cast this
    exact no_small N hN (a + d) (k + m) (by linear_combination hk + hm) ht

end GlobalTheory.KZ
