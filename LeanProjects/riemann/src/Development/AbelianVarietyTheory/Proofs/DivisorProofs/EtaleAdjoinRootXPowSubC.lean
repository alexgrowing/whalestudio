import Mathlib
open IsLocalRing Polynomial

namespace GlobalTheory

theorem etale_adjoinRoot_X_pow_sub_C : ∀ (R : Type) [CommRing R] (n : ℕ) (u : R), IsUnit (n : R) →
    IsUnit u → Algebra.Etale R (AdjoinRoot (Polynomial.X ^ n - Polynomial.C u : Polynomial R)) := by
  intro R _ n u hn hu
  set f : R[X] := X ^ n - C u with hfdef
  have key : f.Monic ∧ IsUnit (AdjoinRoot.mk f (derivative f)) := by
    by_cases hn0 : n = 0
    · subst hn0
      have h01 : (0 : R) = 1 := isUnit_zero_iff.1 (by simpa using hn)
      have : Subsingleton R := subsingleton_of_zero_eq_one h01
      have : Subsingleton (AdjoinRoot f) := (AdjoinRoot.of f).codomain_trivial
      exact ⟨Subsingleton.elim _ _, isUnit_of_subsingleton _⟩
    have hm : f.Monic := monic_X_pow_sub_C _ hn0
    have h1 : AdjoinRoot.root f ^ n = algebraMap R _ u := by
      have := AdjoinRoot.eval₂_root f
      simpa [hfdef, sub_eq_zero] using this
    have hr : IsUnit (AdjoinRoot.root f) :=
      (isUnit_pow_iff hn0).1 (h1 ▸ hu.map _)
    refine ⟨hm, ?_⟩
    have e : AdjoinRoot.mk f (derivative f) = algebraMap R _ (n : R) * AdjoinRoot.root f ^ (n - 1) := by
      simp [hfdef, derivative_X_pow, AdjoinRoot.algebraMap_eq]
    rw [e]
    exact (hn.map _).mul (hr.pow _)
  obtain ⟨hm, h⟩ := key
  let P : StandardEtalePair R := ⟨f, hm, derivative f, 1, 0, 1, by simp⟩
  exact .of_equiv (P.equivAwayAdjoinRoot.trans
    ((IsLocalization.atUnit _ (Localization.Away (AdjoinRoot.mk f (derivative f))) _
      h).symm.restrictScalars R))

end GlobalTheory
