import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BoundAtTwoAndThreeForFamily
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GlobalCore
import Formalism.SharpRestriction.LevelLetterCocycles.IdempotentChoiceDepthZero
import Formalism.SharpRestriction.LevelLetterCocycles.TableLineDegreeTwo
import Formalism.SharpRestriction.LevelLetterCocycles.AdmissibleParameterJ
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.BaseSizes
import Formalism.SharpRestriction.LevelLetterCocycles.NEqRZeroMulXPow
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut

noncomputable section

namespace GlobalTheory.LevelBelowStarBound.QdSmall

theorem qd_lt_lStar_at {D : D7} (L : SizeData₂ D) (P : ParameterChoice' D L)
    (hy : Real.exp 1 ≤ L.sc.x ^ (L.sc.eps / 3)) :
    (D.host.q : ℝ) < LevelStarExponents.lStar L ∧ (D.host.d : ℝ) < LevelStarExponents.lStar L ∧ ∀ p ∈ D.host.small, (p : ℝ) < LevelStarExponents.lStar L := by
  have hx1 : 1 < L.sc.x := L.sc.one_lt_alt
  have hx0 : 0 < L.sc.x := by linarith
  set y := L.sc.x ^ (L.sc.eps / 3) with hydef
  have hL : L.sc.L = y ^ 3 := by
    unfold Scale.L
    rw [hydef, ← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
    congr 1; push_cast; ring
  have he2 : (2 : ℝ) < Real.exp 1 := by
    have := Real.add_one_lt_exp (x := (1 : ℝ)) one_ne_zero; linarith
  have hy2 : 2 < y := lt_of_lt_of_le he2 hy

  have hkey : L.sc.L / 72 < L.sc.L - y := by
    rw [hL]
    have hy0 : 0 ≤ y := by linarith
    have h4 : 4 ≤ y ^ 2 := by nlinarith
    have : 4 * y ≤ y ^ 3 := by nlinarith [mul_le_mul_of_nonneg_left h4 hy0]
    nlinarith

  have hb' : Real.exp (L.sc.L - y) ≤ L.sc.b' := by
    unfold Scale.b' Scale.a Scale.X' Scale.b
    rw [← hydef, Real.exp_sub, mul_div_assoc]
    have : 0 ≤ Real.exp L.sc.L / Real.exp y := by positivity
    nlinarith

  have hn1 : (1 : ℝ) ≤ D.R.n := Formalism.MainNotions.TwistedPlaces.n_ge_one D
  have ht1 : (1 : ℝ) ≤ D.R.t := Formalism.MainNotions.TwistedPlaces.t_ge_one D
  have hc := P.condE_le
  have hc0 : (0 : ℝ) ≤ (LevelStarExponents.condE D : ℝ) := by positivity
  have hc36 : (LevelStarExponents.condE D : ℝ) ^ 36 ≤ Real.exp (L.sc.L / 72) ^ 36 := by
    have h1 : (1 : ℝ) ≤ (D.R.t : ℝ) ^ 150 := one_le_pow₀ ht1
    have h2 : (LevelStarExponents.condE D : ℝ) ^ 36 ≤ (LevelStarExponents.condE D : ℝ) ^ 36 * (D.R.t : ℝ) ^ 150 :=
      le_mul_of_one_le_right (by positivity) h1
    have h3 : L.sc.b ^ ((1 : ℝ) / 2) = Real.exp (L.sc.L / 72) ^ 36 := by
      unfold Scale.b
      rw [← Real.exp_mul, ← Real.exp_nat_mul]
      congr 1; push_cast; ring
    linarith
  have hcE : (LevelStarExponents.condE D : ℝ) ≤ Real.exp (L.sc.L / 72) :=
    (pow_le_pow_iff_left₀ hc0 (Real.exp_pos _).le (by norm_num)).1 hc36
  have hlt : (LevelStarExponents.condE D : ℝ) < L.sc.b' :=
    lt_of_le_of_lt hcE (lt_of_lt_of_le (Real.exp_lt_exp.2 hkey) hb')
  have hstar : L.sc.b' < LevelStarExponents.lStar L := Formalism.MainNotions.TwistedPlaces.lStar_gt L P

  obtain ⟨hq, hd⟩ := P.qd_pow
  have hxp : 0 < L.sc.x ^ (2 * L.Ct + 5) := Real.rpow_pos_of_pos hx0 _
  have hq0 : 1 ≤ D.host.q := by
    have : (0 : ℝ) < D.host.q := lt_trans hxp hq
    exact_mod_cast this
  have hd0 : 1 ≤ D.host.d := by
    have : (0 : ℝ) < D.host.d := lt_trans hxp hd
    exact_mod_cast this
  have hS0 : 1 ≤ D.host.QS := D.host.QS_pos
  have hcv : LevelStarExponents.condE D = D.host.QS * D.host.q * D.host.d := rfl
  have hqC : D.host.q ≤ LevelStarExponents.condE D := by
    rw [hcv]
    calc D.host.q = 1 * D.host.q * 1 := by ring
      _ ≤ D.host.QS * D.host.q * D.host.d := by gcongr
  have hdC : D.host.d ≤ LevelStarExponents.condE D := by
    rw [hcv]
    calc D.host.d = 1 * 1 * D.host.d := by ring
      _ ≤ D.host.QS * D.host.q * D.host.d := by gcongr
  have hSC : D.host.QS ≤ LevelStarExponents.condE D := by
    rw [hcv]
    calc D.host.QS = D.host.QS * 1 * 1 := by ring
      _ ≤ D.host.QS * D.host.q * D.host.d := by gcongr
  have hqC' : (D.host.q : ℝ) ≤ LevelStarExponents.condE D := by exact_mod_cast hqC
  have hdC' : (D.host.d : ℝ) ≤ LevelStarExponents.condE D := by exact_mod_cast hdC
  refine ⟨by linarith, by linarith, fun p hp => ?_⟩
  have hpC : (p : ℝ) ≤ LevelStarExponents.condE D := by exact_mod_cast (Nat.le_of_mem_primeFactors hp).trans hSC
  linarith

theorem qd_lt_lStar : ∀ {eps : ℝ} (Fm : FamP eps), ∃ x0 : ℝ, ∀ x ≥ x0, Fm.x1 < x → ∀ (a : Fm.Ix x),
    ((Fm.D x a).host.q : ℝ) < LevelStarExponents.lStar (Fm.L x a) ∧ ((Fm.D x a).host.d : ℝ) < LevelStarExponents.lStar (Fm.L x a) ∧
      ∀ p ∈ (Fm.D x a).host.small, (p : ℝ) < LevelStarExponents.lStar (Fm.L x a) := by
  intro eps Fm
  refine ⟨Real.exp (3 / eps), fun x hx0 hx a => ?_⟩
  apply qd_lt_lStar_at (Fm.L x a) (Fm.params x hx a)
  have hX := Fm.L_x x a hx
  have hE := Fm.L_eps x a
  have hpos : 0 < eps := hE ▸ (Fm.L x a).sc.eps_pos
  rw [hX, hE]
  have h3 : 0 < eps / 3 := by positivity
  calc Real.exp 1 = Real.exp (3 / eps) ^ (eps / 3) := by
        rw [← Real.exp_mul]; congr 1; field_simp
    _ ≤ x ^ (eps / 3) := Real.rpow_le_rpow (Real.exp_pos _).le hx0 h3.le

end GlobalTheory.LevelBelowStarBound.QdSmall

end
