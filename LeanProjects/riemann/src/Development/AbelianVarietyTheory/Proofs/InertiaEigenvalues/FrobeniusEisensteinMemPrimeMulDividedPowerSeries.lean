import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NatCastNeZeroPs

noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter GlobalTheory.CrysPrism
open scoped Formalism.Per

namespace GlobalTheory.CrysPrism

theorem frobS_eis_mem : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O]
    [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K]
    [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O),
    ∃ B ∈ SdSet t K e, inclS t K (frobS l a (eis l a e)) = (l : ZMod a → K⟦X⟧) * B := by
  intro l hl a e _ _ O K _ _ _ _ _ _ _ _ _ t
  have hlp : l.Prime := hl.out
  have hl0 : (l : K) ≠ 0 := by
    have h : (l : K) = algebraMap ℚ_[l] K (l : ℚ_[l]) := by simp
    rw [h]
    exact (map_ne_zero _).2 (Nat.cast_ne_zero.2 hlp.ne_zero)
  have hle : l * e ≠ 0 := Nat.mul_ne_zero hlp.ne_zero (NeZero.ne e)
  have hf : frobS l a (eis l a e) = X ^ (l * e) + (l : (Wq l a)⟦X⟧) := by
    simp [eis, pow_mul]
  refine ⟨fun _ => 1 + C (l : K)⁻¹ * X ^ (l * e),
    ⟨fun n => if n = 0 then 1 else if n = l * e then (((l - 1).factorial : ℕ) : Wq l a) else 0, ?_, ?_⟩, ?_⟩
  · intro r
    rw [Filter.eventually_cofinite]
    refine (Set.finite_le_nat (l * e)).subset fun n hn => ?_
    by_contra h
    simp only [Set.mem_setOf_eq, not_le] at h
    apply hn
    simp only [show n ≠ 0 by omega, show n ≠ l * e by omega, if_false]
    exact dvd_zero _
  · intro τ n
    rw [map_add, coeff_one, coeff_C_mul, coeff_X_pow]
    by_cases h0 : n = 0
    · subst h0
      simp [hle.symm]
    · by_cases h1 : n = l * e
      · subst h1
        have hfac : (l : K)⁻¹ * (l.factorial : K) = ((l - 1).factorial : K) := by
          rw [← Nat.mul_factorial_pred hlp.ne_zero, Nat.cast_mul, ← mul_assoc, inv_mul_cancel₀ hl0, one_mul]
        simp only [h0, hle, if_false, if_true, zero_add, mul_one, map_natCast]
        rw [Nat.mul_div_cancel _ (Nat.pos_of_ne_zero (NeZero.ne e)), mul_comm, hfac]
      · simp [h0, h1]
  · funext τ
    ext n
    rw [inclS_apply, coeff_toAc, hf, Pi.mul_apply, Pi.natCast_apply, ← map_natCast (C : K →+* K⟦X⟧),
      coeff_C_mul, map_add (coeff n) (X ^ (l * e)) (l : (Wq l a)⟦X⟧), map_add (coeff n) (1 : K⟦X⟧), coeff_one, coeff_C_mul, coeff_X_pow, coeff_X_pow,
      ← map_natCast (C : Wq l a →+* (Wq l a)⟦X⟧), coeff_C]
    by_cases h0 : n = 0
    · subst h0
      simp [hle.symm]
    · by_cases h1 : n = l * e
      · subst h1
        simp [h0, hl0]
      · simp [h0, h1]

end GlobalTheory.CrysPrism
