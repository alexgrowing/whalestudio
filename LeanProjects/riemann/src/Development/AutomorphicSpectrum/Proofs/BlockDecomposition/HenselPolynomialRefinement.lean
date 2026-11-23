import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.IsCompl
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsEvalEqProdOfNatDegreeEq
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MulProdCongr

open TensorProduct CrystallineSemistableComparison.D
open scoped LaurentPolynomial

namespace GlobalTheory.CompanionTheory.AicStep

open Polynomial in

theorem aic_step : ∀ (B : Type) [CommRing B] (T : Type) [CommRing T] (π : B) (g : B →+* T), IsCompl π g → π ∈ nonZeroDivisors B → AIC B → VAL π → ∀ P : Polynomial T, P.Monic → 0 < P.natDegree → ∀ (M : ℕ) (a : B), P.eval (g a) ∈ Ideal.span {g π ^ (P.natDegree * M)} → ∃ a₁ : B, a₁ - a ∈ Ideal.span {π ^ M} ∧ P.eval (g a₁) ∈ Ideal.span {g π ^ (P.natDegree * (M + 1))} := by
  intro B _ T _ π g hC hπ hA hV P hP hd M a ha
  obtain ⟨_, hsurj, hinj⟩ := hC
  haveI : Nontrivial T := by
    by_contra hT
    rw [not_nontrivial_iff_subsingleton] at hT
    have hP0 : P = 0 := Polynomial.ext fun n => Subsingleton.elim _ _
    rw [hP0, natDegree_zero] at hd
    exact lt_irrefl _ hd
  haveI : Nontrivial B := g.domain_nontrivial
  choose c hc using fun i : ℕ => hsurj (P.natDegree * (M + 1)) (P.coeff i)
  have hsum : (∑ i ∈ Finset.range P.natDegree, C (c i) * X ^ i : B[X]) =
      ∑ i : Fin P.natDegree, C (c i) * X ^ (i : ℕ) :=
    (Fin.sum_univ_eq_sum_range (fun i => (C (c i) * X ^ i : B[X])) _).symm
  let Q : B[X] := X ^ P.natDegree + ∑ i ∈ Finset.range P.natDegree, C (c i) * X ^ i
  have hQm : Q.Monic := by
    show (X ^ P.natDegree + ∑ i ∈ Finset.range P.natDegree, C (c i) * X ^ i : B[X]).Monic
    rw [hsum]
    exact monic_X_pow_add (degree_sum_fin_lt _)
  have hQd : Q.natDegree = P.natDegree := by
    show (X ^ P.natDegree + ∑ i ∈ Finset.range P.natDegree, C (c i) * X ^ i : B[X]).natDegree = _
    rw [hsum, natDegree_add_eq_left_of_degree_lt, natDegree_X_pow]
    rw [degree_X_pow]
    exact degree_sum_fin_lt _
  have key : ∀ x : B, P.eval (g x) - g (Q.eval x) ∈ Ideal.span {g π ^ (P.natDegree * (M + 1))} := by
    intro x
    have e : P.eval (g x) - g (Q.eval x) =
        ∑ i ∈ Finset.range P.natDegree, (P.coeff i - g (c i)) * g x ^ i := by
      conv_lhs => rw [hP.as_sum]
      simp only [Q, eval_add, eval_pow, eval_X, eval_finsetSum, eval_mul, eval_C, map_add, map_pow,
        map_sum, map_mul, sub_mul, Finset.sum_sub_distrib]
      ring
    rw [e]
    exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_right _ _ (hc i)
  obtain ⟨b, hb⟩ := GlobalTheory.CompanionTheory.AicSplit.exists_eval_eq_prod_of_natDegree_eq
    (fun p hp hpd => hA p hp hpd) P.natDegree Q hQm hQd
  have hle : Ideal.span {g π ^ (P.natDegree * (M + 1))} ≤ Ideal.span {g π ^ (P.natDegree * M)} :=
    Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow _ (by gcongr; omega))
  have h1 : g (Q.eval a) ∈ Ideal.span {g π ^ (P.natDegree * M)} := by
    have h := Ideal.sub_mem _ ha (hle (key a))
    rwa [sub_sub_cancel] at h
  have h2 := hinj _ _ h1
  rw [hb a] at h2
  obtain ⟨a₁, ha₁, h0⟩ := GlobalTheory.CompanionTheory.RootNear.root_near B π hπ hV P.natDegree M b a hd h2
  refine ⟨a₁, ha₁, ?_⟩
  have h3 := key a₁
  rwa [hb a₁, h0, map_zero, sub_zero] at h3

end GlobalTheory.CompanionTheory.AicStep
