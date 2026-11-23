import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqOneOfPowEqOne
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc

namespace GlobalTheory.InertFix

theorem eq_one_of_pow_eq_one {K : Type*} [NormedField K] [IsUltrametricDist K] (m : ℕ)
    (hm : ‖(m : K)‖ = 1) (u : K) (hu : u ^ m = 1) (h1 : ‖u - 1‖ < 1) : u = 1 := by
  first
  | exact @_root_.GlobalTheory.PowerEqOneClose.eq_one_of_pow_eq_one
  | exact _root_.GlobalTheory.PowerEqOneClose.eq_one_of_pow_eq_one
  | (apply _root_.GlobalTheory.PowerEqOneClose.eq_one_of_pow_eq_one <;> assumption)
  | (intros; apply _root_.GlobalTheory.PowerEqOneClose.eq_one_of_pow_eq_one <;> assumption)
  | (intros; apply @_root_.GlobalTheory.PowerEqOneClose.eq_one_of_pow_eq_one <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.PowerEqOneClose.eq_one_of_pow_eq_one ..)

theorem inertia_fix : ∀ (l : ℕ) [Fact l.Prime] (n : ℕ), 0 < n → ∀ σ : GQ l,
    (∀ x : Om l, ‖x‖ ≤ 1 → ‖σ x - x‖ < 1) → ∀ x : Om l, x ^ l ^ n = x → σ x = x := by
  intro l hl n hn σ hσ x hx
  by_cases hx0 : x = 0
  · rw [hx0, map_zero]
  have hlp : 1 < l ^ n := Nat.one_lt_pow hn.ne' hl.out.one_lt
  obtain ⟨m, hm⟩ : ∃ m, l ^ n = m + 1 := ⟨l ^ n - 1, by omega⟩
  have hm0 : m ≠ 0 := by omega
  have hxm : x ^ m = 1 := by
    rw [hm, pow_succ] at hx
    exact mul_right_cancel₀ hx0 (by rw [hx, one_mul])
  have hnx : ‖x‖ = 1 := by
    have : ‖x‖ ^ m = 1 := by rw [← norm_pow, hxm, norm_one]
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hm0).1 this
  have hcop : l.Coprime m := by
    have h : (l ^ n).Coprime m := by rw [hm]; simp
    exact Nat.Coprime.of_dvd_left (dvd_pow_self l hn.ne') h
  have hmn : ‖(m : Om l)‖ = 1 := by
    rw [← map_natCast (algebraMap ℚ_[l] (PadicAlgCl l)), PadicAlgCl.norm_extends]
    exact Padic.norm_natCast_eq_one_iff.2 hcop
  have hu : σ x / x = 1 := by
    refine eq_one_of_pow_eq_one m hmn _ ?_ ?_
    · rw [div_pow, ← map_pow, hxm, map_one, div_one]
    · have e : σ x / x - 1 = (σ x - x) / x := by field_simp
      rw [e, norm_div, hnx, div_one]
      exact hσ x hnx.le
  exact (div_eq_one_iff_eq hx0).1 hu

end GlobalTheory.InertFix
