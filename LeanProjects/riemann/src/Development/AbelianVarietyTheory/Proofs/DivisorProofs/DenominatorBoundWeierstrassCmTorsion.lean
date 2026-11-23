import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTrSelf
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.TranslateProduct
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModDefs
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationBoundMultiplierSqrtNegDStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraicValuationBoundAtRamifiedPrimeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationBoundThreeInertStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsogenyFormulaWeierstrassPIntegralStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraicValuationAtLeastBasicPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralWeierstrassPTorsionNonrealMultiplierStatement

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open NumberField GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.LatVal ReciprocityTheory.ChartRestriction.L1 Formalism.L2.Th1.F
open GlobalTheory.CMVal GlobalTheory.HeckeGal
open ModularForm (E₄ E₆)

namespace GlobalTheory.CMSize

theorem mulStable_one_add {L : PeriodPair} {w : ℂ} (h : MulStable L w) : MulStable L (1 + w) := by
  intro x hx
  rw [add_mul, one_mul]
  exact add_mem hx (h x hx)

theorem mulStable_one_sub {L : PeriodPair} {w : ℂ} (h : MulStable L w) : MulStable L (1 - w) := by
  intro x hx
  rw [sub_mul, one_mul]
  exact sub_mem hx (h x hx)

theorem main : ∀ (l : ℕ) [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) (d : ℕ) (L : PeriodPair) (Ω P : ℂ) (M : ℕ), d.Prime → 4 < d → MulStable L (Complex.I * (Real.sqrt d : ℝ)) → Ω ^ 12 = latDisc L → ¬ l ∣ M → P ∉ L.lattice → (M : ℂ) * P ∈ L.lattice → Sz l lam (if l = 2 then (if d % 4 = 3 then 1 else 2) else if l = d then 1 / 2 else 0) ((s2 L + L.weierstrassP P) / Ω ^ 2) := by
  intro l hl lam d L Ω P M hd hd4 hw hΩ hM hP hMP
  have hlp : l.Prime := hl.out
  have hM0 : 0 < M := Nat.pos_of_ne_zero (by rintro rfl; exact hM (dvd_zero _))
  have hs : Real.sqrt d * Real.sqrt d = d := Real.mul_self_sqrt (Nat.cast_nonneg d)
  have hs0 : Real.sqrt d ≠ 0 := by
    have : (0 : ℝ) < d := by exact_mod_cast hd.pos
    exact (Real.sqrt_pos.mpr this).ne'
  set w : ℂ := Complex.I * (Real.sqrt d : ℝ) with hwdef
  have hre : w.re = 0 := by simp [hwdef]
  have him : w.im = Real.sqrt d := by simp [hwdef]
  have him0 : w.im ≠ 0 := by rw [him]; exact hs0
  have hw2 : w ^ 2 = -(d : ℂ) := by
    have h1 : ((Real.sqrt d : ℝ) : ℂ) * ((Real.sqrt d : ℝ) : ℂ) = d := by
      rw [← Complex.ofReal_mul, hs]; simp
    rw [hwdef, mul_pow, Complex.I_sq, sq, h1]; ring
  have hn0 : Complex.normSq w = (d : ℕ) := by
    rw [Complex.normSq_apply, hre, him, hs]; simp
  have hn1 : Complex.normSq (1 + w) = ((1 + d : ℕ) : ℝ) := by
    rw [Complex.normSq_apply]; simp [hre, him, hs]
  have hn2 : Complex.normSq (1 - w) = ((1 + d : ℕ) : ℝ) := by
    rw [Complex.normSq_apply]; simp [hre, him, hs]
  have hsz := (GlobalTheory.T.algebraicValuationAtLeast_basic_properties l lam).1
  have hp : Sz l lam 0 (12 * (L.weierstrassP P / Ω ^ 2)) := by
    refine hsz (M ^ 2) _ (fun h => hM (hlp.dvd_of_dvd_pow h)) ?_
    have := ((GlobalTheory.T.isIntegral_weierstrassP_torsion_nonreal_multiplier L w Ω M hw him0 hΩ hM0).1 P hMP).1
    convert this using 1
    push_cast; ring
  have key : ∀ (α : ℂ) (n : ℕ), MulStable L α → Complex.normSq α = n → ¬ l ∣ n →
      Sz l lam 0 ((α ^ 2 - n) * ((s2 L + L.weierstrassP P) / Ω ^ 2) -
        (α ^ 2 - 1) * (L.weierstrassP P / Ω ^ 2)) := by
    intro α n hα hn hln
    have hn0 : 0 < n := Nat.pos_of_ne_zero (by rintro rfl; exact hln (dvd_zero _))
    refine hsz ((M * n) ^ 2) _ (fun h => ?_) ?_
    · rcases (Nat.Prime.dvd_mul hlp).1 (hlp.dvd_of_dvd_pow h) with h | h
      · exact hM h
      · exact hln h
    · have := GlobalTheory.T.isogeny_formula_weierstrassP_integral L α w Ω P M n hw him0 hΩ hα hn hn0 hM0 hP hMP
      rwa [Nat.cast_pow]
  by_cases hld : l = d
  · subst hld
    rw [if_neg (by omega), if_pos rfl]
    have hnd : ¬ l ∣ 1 + l := by
      intro h
      have : l ∣ 1 := (Nat.dvd_add_left (dvd_refl l)).1 h
      exact hlp.one_lt.ne' (Nat.dvd_one.1 this)
    have h1 := key (1 + w) (1 + l) (mulStable_one_add hw) hn1 hnd
    refine GlobalTheory.T.algebraicValuation_bound_at_ramified_prime l lam w _ _ hd4 hw2 hp ?_
    simpa only [Nat.cast_add, Nat.cast_one] using h1
  · rw [if_neg hld]
    by_cases h3 : l = 3 ∧ d % 3 = 1
    · obtain ⟨rfl, h3⟩ := h3
      rw [if_neg (by omega)]
      have hnd : ¬ 3 ∣ 1 + d := by omega
      have h1 := key (1 + w) (1 + d) (mulStable_one_add hw) hn1 hnd
      have h2 := key (1 - w) (1 + d) (mulStable_one_sub hw) hn2 hnd
      refine GlobalTheory.T.valuation_bound_three_inert lam d w _ (L.weierstrassP P / Ω ^ 2) h3 hw2 ?_ ?_
      · simpa only [Nat.cast_add, Nat.cast_one] using h1
      · simpa only [Nat.cast_add, Nat.cast_one] using h2
    · have hnd : ¬ l ∣ d := fun h => hld ((Nat.prime_dvd_prime_iff_eq hlp hd).1 h)
      have h1 := key w d hw hn0 hnd
      refine GlobalTheory.T.valuation_bound_multiplier_sqrt_neg_d l lam d _ _ hd hd4 hld hp ?_ ?_
      · convert h1 using 1
        rw [hw2]; ring
      · rintro rfl
        have : ¬ d % 3 = 1 := fun h => h3 ⟨rfl, h⟩
        omega

end GlobalTheory.CMSize
