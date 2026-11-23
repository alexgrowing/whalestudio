import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffOfW
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter GlobalTheory.CrysPrism
open scoped Formalism.Per

namespace GlobalTheory.CrysPrism

theorem ofW_single : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O), ∀ (i n : ℕ) (c : Wq l a), ofW t K e (Pi.single (i, n) c) = cstW t K c * uFam a K ^ (n % e) * dFam a K e (n / e) * xFam a K i := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ t i n c
  funext τ
  have hR : (cstW t K c * uFam a K ^ (n % e) * dFam a K e (n / e) * xFam a K i) τ
      = C (C (algebraMap O K (emb t τ c) / (dpDen e i n : K)) * X ^ n) * X ^ i := by
    simp only [Pi.mul_apply, Pi.pow_apply, cstW, uFam, dFam, xFam]
    have h1 : (X : K⟦X⟧) ^ n = X ^ (n % e) * X ^ (e * (n / e)) := by
      rw [← pow_add, Nat.mod_add_div]
    rw [h1, dpDen, Nat.cast_mul, div_eq_mul_inv, mul_inv]
    simp only [map_mul, map_pow]
    ring
  rw [hR]
  ext i' n'
  rw [coeff_ofW, coeff_C_mul, coeff_X_pow, Pi.single_apply]
  by_cases hi : i' = i
  · subst hi
    by_cases hn : n' = n
    · subst hn
      simp [coeff_C_mul, coeff_X_pow]
    · simp [coeff_C_mul, coeff_X_pow, hn]
  · simp [hi]

end GlobalTheory.CrysPrism
