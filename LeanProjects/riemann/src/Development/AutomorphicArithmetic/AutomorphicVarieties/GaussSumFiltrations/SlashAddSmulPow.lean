import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.EvenPos
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

namespace GlobalTheory.HilbertThetaSeries

theorem slash_add_smul_pow : ∀ (F : Type) [Field F] [NumberField F] (k M : ℕ) (h : GL (Fin 2) (InfinitePlace F → ℝ)) (f g : Hn F → ℂ) (c : ℂ), sl0 k h (f + g) = sl0 k h f + sl0 k h g ∧ sl0 k h (c • f) = c • sl0 k h f ∧ sl0 (k * M) h (f ^ M) = sl0 k h f ^ M ∧ sl k h (f + g) = sl k h f + sl k h g ∧ sl k h (c • f) = c • sl k h f ∧ sl (k * M) h (f ^ M) = sl k h f ^ M := by
  intro F _ _ k M h f g c
  have h0a : sl0 k h (f + g) = sl0 k h f + sl0 k h g := by
    funext z; simp only [sl0, Pi.add_apply]; ring
  have h0s : sl0 k h (c • f) = c • sl0 k h f := by
    funext z; simp only [sl0, Pi.smul_apply, smul_eq_mul]; ring
  have h0p : sl0 (k * M) h (f ^ M) = sl0 k h f ^ M := by
    funext z; simp only [sl0, Pi.pow_apply]; rw [mul_pow, pow_mul]
  refine ⟨h0a, h0s, h0p, ?_, ?_, ?_⟩
  · funext z; simp only [sl, h0a, Pi.add_apply]; ring
  · funext z; simp only [sl, h0s, Pi.smul_apply, smul_eq_mul]; ring
  · funext z
    simp only [sl, h0p, Pi.pow_apply]
    rw [mul_pow]
    congr 1
    have hx : (0 : ℝ) ≤ ∏ v, |(h : Matrix (Fin 2) (Fin 2) (InfinitePlace F → ℝ)).det v| :=
      Finset.prod_nonneg fun v _ => abs_nonneg _
    rw [← Complex.ofReal_pow, ← Real.rpow_mul_natCast hx]
    congr 2
    push_cast; ring

end GlobalTheory.HilbertThetaSeries
