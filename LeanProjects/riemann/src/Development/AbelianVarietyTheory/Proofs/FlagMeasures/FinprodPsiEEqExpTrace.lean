import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.PsiEDef
import Formalism.LocalRingCardinality.DataSpaces
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TraceEqSumLocalTracesAbovePrime
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.T2SpaceIsNonarchimedeanLocalFieldSingleBlock
open NumberField IsDedekindDomain Formalism.MainNotions.S.Loc ValuativeRel
open scoped nonZeroDivisors

namespace GlobalTheory.AddCharProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem main_prime_pow (h2 : Module.finrank F E = 2) {sig : E →ₐ[F] E}
    (A : ∀ p : HeightOneSpectrum (𝓞 F), LocAt F E sig p) {l : ℕ} (hl : l.Prime) (y : E)
    (hy : IsIntegral ℤ y) (k : ℕ) :
    (Function.mulSupport fun p => (A p).psiE ((A p).ιE (y / (l : E) ^ k))).Finite ∧
      ∏ᶠ p, (A p).psiE ((A p).ιE (y / (l : E) ^ k)) =
        Complex.exp (2 * Real.pi * Complex.I * (((Algebra.trace ℚ E (y / (l : E) ^ k) : ℚ) : ℂ))) :=
  _root_.GlobalTheory.ResidueCharacterDense.prod_psi h2 A hl y hy k

theorem finprod_psiE_eq_exp_trace : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E], Formalism.BasicNotions.CMData F E → ∀ (sig : E →ₐ[F] E), (∀ x, sig x = star x) → ∀ (A : ∀ p : HeightOneSpectrum (𝓞 F), LocAt F E sig p), ∀ x : E, (Function.mulSupport fun p => (A p).psiE ((A p).ιE x)).Finite ∧ ∏ᶠ p, (A p).psiE ((A p).ιE x) = Complex.exp (2 * Real.pi * Complex.I * (((Algebra.trace ℚ E x : ℚ) : ℂ))) := by
  intro F E _ _ _ _ _ _ hc sig _ A x
  let P : E → Prop := fun x => (Function.mulSupport fun p => (A p).psiE ((A p).ιE x)).Finite ∧
    ∏ᶠ p, (A p).psiE ((A p).ιE x) =
      Complex.exp (2 * Real.pi * Complex.I * (((Algebra.trace ℚ E x : ℚ) : ℂ)))
  have hadd : ∀ u v, P u → P v → P (u + v) := by
    rintro u v ⟨hu, hu'⟩ ⟨hv, hv'⟩
    have e : (fun p => (A p).psiE ((A p).ιE (u + v))) =
        fun p => (A p).psiE ((A p).ιE u) * (A p).psiE ((A p).ιE v) := by
      funext p
      rw [map_add, AddChar.map_add_eq_mul]
    refine ⟨?_, ?_⟩
    · rw [e]
      exact (hu.union hv).subset (Function.mulSupport_mul _ _)
    · rw [e, finprod_mul_distrib hu hv, hu', hv', ← Complex.exp_add, map_add, Rat.cast_add, mul_add]
  have key : ∀ N : ℕ, N ≠ 0 → ∀ y : E, IsIntegral ℤ y → P (y / (N : E)) := by
    intro N
    induction N using Nat.recOnPosPrimePosCoprime with
    | prime_pow l k hl _ =>
      intro _ y hy
      have := main_prime_pow hc.deg2 A hl y hy k
      simpa only [Nat.cast_pow] using this
    | zero => intro h; exact absurd rfl h
    | one =>
      intro _ y hy
      have := main_prime_pow hc.deg2 A Nat.prime_two y hy 0
      simpa only [pow_zero, Nat.cast_one] using this
    | coprime a b ha hb hab iha ihb =>
      intro _ y hy
      obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.2 hab
      have ha0 : (a : E) ≠ 0 := by exact_mod_cast (by omega : a ≠ 0)
      have hb0 : (b : E) ≠ 0 := by exact_mod_cast (by omega : b ≠ 0)
      have huv' : (u : E) * a + v * b = 1 := by exact_mod_cast huv
      have e : y / ((a * b : ℕ) : E) = (v * y) / a + (u * y) / b := by
        push_cast
        field_simp
        linear_combination (-y) * huv'
      rw [e]
      exact hadd _ _ (iha (by omega) _ ((isIntegral_algebraMap (x := v)).mul hy))
        (ihb (by omega) _ ((isIntegral_algebraMap (x := u)).mul hy))
  have halg : IsAlgebraic ℤ x := (IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 (Algebra.IsAlgebraic.isAlgebraic x)
  obtain ⟨n, hn, hi⟩ := halg.exists_integral_multiple
  have hi' : IsIntegral ℤ ((n * n : ℤ) • x) := by
    rw [mul_smul]; exact hi.smul n
  have h := key (n * n).natAbs (by simpa using hn) _ hi'
  have e : ((n * n : ℤ) • x) / (((n * n).natAbs : ℕ) : E) = x := by
    have h1 : (((n * n).natAbs : ℕ) : E) = ((n * n : ℤ) : E) := by
      rw [← Int.cast_natCast, Int.natAbs_of_nonneg (mul_self_nonneg n)]
    have h0 : ((n * n : ℤ) : E) ≠ 0 := by exact_mod_cast mul_ne_zero hn hn
    rw [h1, zsmul_eq_mul, mul_div_cancel_left₀ _ h0]
  rw [e] at h
  exact h

end GlobalTheory.AddCharProduct
