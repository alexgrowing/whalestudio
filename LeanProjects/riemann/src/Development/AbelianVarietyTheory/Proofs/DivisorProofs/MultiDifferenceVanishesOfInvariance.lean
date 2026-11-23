import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsAtOfNorms
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsLinearMapMultilinearMapBaseChange
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.VertForm GlobalTheory.TrivFlag GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.TrueCx
open scoped Classical

namespace GlobalTheory.FinDiffPow

theorem sum_multiDiff_eq_zero : ∀ (A : Type 1) [AddCommGroup A] (f : A → ℤ) (d : ℕ), DiffVanish (d + 1) f → ∀ (N : ℕ) (g : Fin N → A) (p : ℕ), 2 ≤ p → (∀ (a : ℕ) (c : A), ∑ i, f (p ^ a • g i + c) = (N : ℤ) * f c) → ∀ (m D : ℕ) (S : Finset (Fin D)), S.Nonempty → ∀ P : Fin D → A, ∑ i, multiDiff (fun j => if j ∈ S then m • g i else P j) f 0 = 0 := by
  intro A _ f d hf N g p hp hsum m D S hS P
  have step1 : ∀ (n : ℤ) (c : A), ∑ i, f (n • g i + c) = (N : ℤ) * f c := by
    intro n c
    have hpoly : ∀ i, ∃ q : Polynomial ℚ, q.natDegree ≤ d ∧
        ∀ n : ℤ, q.eval (n : ℚ) = f (c + n • g i) := fun i ↦ by
      obtain ⟨q, h1, h2, -⟩ := hf.exists_polynomial_int ℚ (g i) c
      exact ⟨q, h1, h2⟩
    choose q _ hq using hpoly
    set Q : Polynomial ℚ := ∑ i, q i - Polynomial.C ((N : ℚ) * f c) with hQdef
    have hQ : ∀ n : ℤ, Q.eval (n : ℚ) = ((∑ i, f (n • g i + c) - (N : ℤ) * f c : ℤ) : ℚ) := by
      intro n
      simp only [hQdef, Polynomial.eval_sub, Polynomial.eval_finset_sum, hq, Polynomial.eval_C]
      push_cast
      simp only [add_comm c]
    have hQ0 : Q = 0 := by
      apply Polynomial.eq_zero_of_infinite_isRoot
      refine Set.infinite_of_injective_forall_mem (f := fun a : ℕ ↦ (((p ^ a : ℕ) : ℤ) : ℚ)) ?_ ?_
      · intro a b hab
        simp only at hab
        have : p ^ a = p ^ b := by exact_mod_cast hab
        exact Nat.pow_right_injective hp this
      · intro a
        show Q.IsRoot _
        rw [Polynomial.IsRoot, hQ]
        simp only [natCast_zsmul, hsum a c, sub_self, Int.cast_zero]
    have := hQ n
    rw [hQ0, Polynomial.eval_zero] at this
    have h0 : (∑ i, f (n • g i + c) - (N : ℤ) * f c : ℤ) = 0 := by exact_mod_cast this.symm
    exact sub_eq_zero.1 h0
  have key : ∀ i (T : Finset (Fin D)),
      f (0 - ∑ j ∈ T, (if j ∈ S then m • g i else P j)) =
        f ((-(((T.filter (· ∈ S)).card * m : ℕ) : ℤ)) • g i +
          (0 - ∑ j ∈ T, (if j ∈ S then (0 : A) else P j))) := by
    intro i T
    congr 1
    rw [Finset.sum_ite, Finset.sum_ite, Finset.sum_const, Finset.sum_const_zero, neg_smul,
      natCast_zsmul, Nat.mul_comm _ m, mul_nsmul]
    abel
  have hQ : multiDiff (fun j ↦ if j ∈ S then (0 : A) else P j) f = 0 := by
    rw [multiDiff_eq_shiftAct]
    obtain ⟨j0, hj0⟩ := hS
    rw [Finset.prod_eq_zero (Finset.mem_univ j0) (by simp [hj0, diffElt_zero]), map_zero]
    rfl
  calc ∑ i, multiDiff (fun j ↦ if j ∈ S then m • g i else P j) f 0
      = ∑ i, ∑ T : Finset (Fin D), (-1 : ℤ) ^ T.card •
          f ((-(((T.filter (· ∈ S)).card * m : ℕ) : ℤ)) • g i +
            (0 - ∑ j ∈ T, (if j ∈ S then (0 : A) else P j))) := by
        simp only [multiDiff_apply, key]
    _ = ∑ T : Finset (Fin D), (-1 : ℤ) ^ T.card •
          ∑ i, f ((-(((T.filter (· ∈ S)).card * m : ℕ) : ℤ)) • g i +
            (0 - ∑ j ∈ T, (if j ∈ S then (0 : A) else P j))) := by
        rw [Finset.sum_comm]; simp only [Finset.smul_sum]
    _ = ∑ T : Finset (Fin D), (-1 : ℤ) ^ T.card •
          ((N : ℤ) * f (0 - ∑ j ∈ T, (if j ∈ S then (0 : A) else P j))) := by
        simp only [step1]
    _ = (N : ℤ) * multiDiff (fun j ↦ if j ∈ S then (0 : A) else P j) f 0 := by
        rw [multiDiff_apply, Finset.mul_sum]
        refine Finset.sum_congr rfl fun T _ ↦ ?_
        simp only [smul_eq_mul]; ring
    _ = 0 := by rw [hQ]; simp

end GlobalTheory.FinDiffPow
