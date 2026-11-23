import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.EvenPos
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

namespace GlobalTheory.HilbertThetaSeries.IdeleAbs

theorem not_dvd_absNorm_of_not_mem {F : Type} [Field F] [NumberField F] (p : ℕ) [hp : Fact p.Prime]
    (w : HeightOneSpectrum (𝓞 F)) (hw : ((p : ℕ) : 𝓞 F) ∉ w.asIdeal) : ¬ p ∣ Ideal.absNorm w.asIdeal := by
  intro h
  have : Finite (𝓞 F ⧸ w.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ w.ne_bot
  have := w.isPrime
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply] at h
  obtain ⟨x, hx⟩ := exists_prime_addOrderOf_dvd_card' p h
  have h1 : ((p : ℕ) : 𝓞 F ⧸ w.asIdeal) * x = 0 := by
    rw [← nsmul_eq_mul, ← hx, addOrderOf_nsmul_eq_zero]
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [addOrderOf_zero] at hx
    exact hp.out.one_lt.ne hx
  have h2 : ((p : ℕ) : 𝓞 F ⧸ w.asIdeal) = 0 := (mul_eq_zero.1 h1).resolve_right hx0
  apply hw
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  simpa using h2

theorem norm_natCast_eq_one (p : ℕ) [Fact p.Prime] (N : ℕ) (h : ¬ p ∣ N) : ‖((N : ℚ) : ℚ_[p])‖ = 1 := by
  rw [Padic.eq_padicNorm]
  exact_mod_cast (padicNorm.nat_eq_one_iff N).2 h

theorem absF_eq_rat (F : Type) [Field F] [NumberField F] (p : ℕ) [Fact p.Prime] (z : (Af F)ˣ)
    (hz : ∀ w : HeightOneSpectrum (𝓞 F), ((p : ℕ) : 𝓞 F) ∈ w.asIdeal → Valued.v (pLoc F w (z : Af F)) = 1) :
    ∃ r : ℚ, 0 < r ∧ ‖(r : ℚ_[p])‖ = 1 ∧ absF z = r := by
  have key : ∃ r : ℚ, 0 < r ∧ ‖(r : ℚ_[p])‖ = 1 ∧ (r : ℝ) = absF z := by
    refine finprod_induction (fun t : ℝ => ∃ r : ℚ, 0 < r ∧ ‖(r : ℚ_[p])‖ = 1 ∧ (r : ℝ) = t) ⟨1, one_pos, by simp, by simp⟩ ?_ ?_
    · rintro _ _ ⟨a, ha, ha', rfl⟩ ⟨b, hb, hb', rfl⟩
      exact ⟨a * b, mul_pos ha hb, by rw [Rat.cast_mul, norm_mul, ha', hb', one_mul], by rw [Rat.cast_mul]⟩
    · intro w
      by_cases hw : ((p : ℕ) : 𝓞 F) ∈ w.asIdeal
      · refine ⟨1, one_pos, by simp, ?_⟩
        rw [FinitePlace.norm_def, hz w hw, map_one]
        simp
      · have hne : Valued.v (pLoc F w (z : Af F)) ≠ 0 :=
          (Valuation.ne_zero_iff _).2 (z.isUnit.map (pLoc F w)).ne_zero
        have hN : 0 < Ideal.absNorm w.asIdeal :=
          Nat.pos_of_ne_zero fun h0 => w.ne_bot (Ideal.absNorm_eq_zero_iff.1 h0)
        refine ⟨(Ideal.absNorm w.asIdeal : ℚ) ^ (WithZero.unzero hne).toAdd, zpow_pos (by exact_mod_cast hN) _, ?_, ?_⟩
        · rw [Rat.cast_zpow, norm_zpow, norm_natCast_eq_one p _ (not_dvd_absNorm_of_not_mem p w hw), one_zpow]
        · rw [FinitePlace.norm_def, WithZeroMulInt.toNNReal_neg_apply _ hne]
          push_cast
          rfl
  obtain ⟨r, h1, h2, h3⟩ := key
  exact ⟨r, h1, h2, h3.symm⟩

end GlobalTheory.HilbertThetaSeries.IdeleAbs
