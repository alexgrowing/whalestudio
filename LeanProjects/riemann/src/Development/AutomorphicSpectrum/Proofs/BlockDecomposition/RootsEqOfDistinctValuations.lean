import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaceConjugationPropertiesCmFieldStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwahoriProjSurjective

open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.BCT GlobalTheory.UnitaryBC Formalism.UG
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.RootsDistinctVal

theorem roots_eq_of_distinct_ord : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (n : ℕ) (y : Fin n → ℤ),
    Function.Injective y → ∀ u u' : Fin n → L, (∀ i, ordL (u i) = y i) → (∀ i, ordL (u' i) = y i) →
      ∏ i, (X - C (u i)) = ∏ i, (X - C (u' i)) → u = u' := by
  intro L _ _ n y hy u u' hu hu' hprod
  funext i
  have h0 : (∏ j, (X - C (u' j))).eval (u i) = 0 := by
    rw [← hprod, Polynomial.eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)
  rw [Polynomial.eval_prod, Finset.prod_eq_zero_iff] at h0
  obtain ⟨j, -, hj⟩ := h0
  have hij : u i = u' j := by simpa [sub_eq_zero] using hj
  have : i = j := hy (by rw [← hu i, ← hu' j, hij])
  rw [hij, this]

end GlobalTheory.CompanionTheory.RootsDistinctVal
