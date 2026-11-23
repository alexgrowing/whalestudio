import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AcrisEqZeroOfForallDvd
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAcrisLogOneAdd
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AevalLogDefect
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LogDefectCoeffEqZeroStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FactorialTruncatedLogAdditivityDefectCoeffDvdStatement

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.LogU

theorem defect_mem {R : Type} [CommRing R] (S : Subring R) (a b : R)
    (ha : ∀ i : ℕ, ∃ g ∈ S, ((i.factorial : ℕ) : R) * g = a ^ i)
    (hb : ∀ j : ℕ, ∃ g ∈ S, ((j.factorial : ℕ) : R) * g = b ^ j) (n : ℕ) :
    ∃ e ∈ S, truncLogF n (a + b + a * b) - truncLogF n a - truncLogF n b =
      ((n.factorial * ((n - 1) / 2).factorial : ℕ) : R) * e := by
  choose A hAS hA using ha
  choose B hBS hB using hb
  have hD : ∀ d : Fin 2 →₀ ℕ, ∃ D : ℤ, (((d 0).factorial * (d 1).factorial : ℕ) : ℤ) *
      MvPolynomial.coeff d (logDefect n) = ((n.factorial * ((n - 1) / 2).factorial : ℕ) : ℤ) * D := by
    intro d
    have hd : Finsupp.single 0 (d 0) + Finsupp.single 1 (d 1) = d := by
      ext x; fin_cases x <;> simp
    by_cases h : d 0 + d 1 < n
    · have := GlobalTheory.T.coeff_logDefect_eq_zero_of_add_lt n (d 0) (d 1) h
      rw [hd] at this
      exact ⟨0, by rw [this]; simp⟩
    · obtain ⟨D, hD⟩ := GlobalTheory.T.factorialTruncatedLogAdditivityDefect_coeff_dvd n (d 0) (d 1) (by omega)
      rw [hd] at hD
      exact ⟨D, hD⟩
  choose D hD using hD
  refine ⟨∑ d ∈ (logDefect n).support, (D d : R) * (A (d 0) * B (d 1)),
    Subring.sum_mem _ fun d _ => Subring.mul_mem _ (intCast_mem S _)
      (Subring.mul_mem _ (hAS _) (hBS _)), ?_⟩
  rw [← aeval_logDefect, MvPolynomial.aeval_def, MvPolynomial.eval₂_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  have hc := congrArg (Int.cast : ℤ → R) (hD d)
  push_cast at hc
  simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, eq_intCast]
  rw [← hA, ← hB]
  push_cast
  linear_combination (A (d 0) * B (d 1)) * hc

theorem isLogJ_add : ∀ (l : ℕ) [Fact l.Prime] (a b : Per.Ainf l) (y y' : Per.Acris l), GlobalTheory.LogU.InJ a →
    GlobalTheory.LogU.InJ b → GlobalTheory.LogU.IsLogJ a y → GlobalTheory.LogU.IsLogJ b y' → GlobalTheory.LogU.IsLogJ (a + b + a * b) (y + y') := by
  intro l _ a b y y' ha hb hy hy' r
  have hl : l.Prime := Fact.out
  obtain ⟨N1, hN1⟩ := hy r
  obtain ⟨N2, hN2⟩ := hy' r
  refine ⟨max (max N1 N2) (2 * l ^ r + 1), fun n hn => ?_⟩
  obtain ⟨sa, hsa, za, hza⟩ := hN1 n (le_of_max_le_left (le_of_max_le_left hn))
  obtain ⟨sb, hsb, zb, hzb⟩ := hN2 n (le_of_max_le_right (le_of_max_le_left hn))
  have hn' : 2 * l ^ r + 1 ≤ n := le_of_max_le_right hn
  have hA : ∀ i : ℕ, ∃ g ∈ (Per.Acris0 l).toSubring, ((i.factorial : ℕ) : Per.AinfP l) * g =
      algebraMap (Per.Ainf l) (Per.AinfP l) a ^ i := fun i => by
    obtain ⟨g, hg⟩ := exists_divPow ha i
    exact ⟨g, g.2, hg⟩
  have hB : ∀ i : ℕ, ∃ g ∈ (Per.Acris0 l).toSubring, ((i.factorial : ℕ) : Per.AinfP l) * g =
      algebraMap (Per.Ainf l) (Per.AinfP l) b ^ i := fun i => by
    obtain ⟨g, hg⟩ := exists_divPow hb i
    exact ⟨g, g.2, hg⟩
  obtain ⟨e, he, hE⟩ := defect_mem _ _ _ hA hB n
  have hdvd : l ^ r ∣ ((n - 1) / 2).factorial := by
    refine Nat.dvd_factorial (pow_pos hl.pos r) ?_
    generalize l ^ r = L at hn' ⊢
    omega
  obtain ⟨q, hq⟩ := hdvd
  let E : Per.Acris0 l := ⟨e, he⟩
  refine ⟨sa + sb + ((l ^ r * q : ℕ) : Per.Acris0 l) * E, ?_,
    za + zb - (q : Per.Acris l) * algebraMap (Per.Acris0 l) (Per.Acris l) E, ?_⟩
  · rw [hq] at hE
    simp only [truncLogF] at hE
    have hEe : ((E : Per.Acris0 l) : Per.AinfP l) = e := rfl
    have hc : (((sa + sb + ((l ^ r * q : ℕ) : Per.Acris0 l) * E : Per.Acris0 l)) : Per.AinfP l) =
        (sa : Per.AinfP l) + (sb : Per.AinfP l) + ((l ^ r * q : ℕ) : Per.AinfP l) * e := by
      simp [hEe]
    rw [hc]
    simp only [map_add, map_mul]
    push_cast at hE ⊢
    linear_combination hsa + hsb - hE
  · simp only [map_add, map_mul, map_natCast]
    push_cast
    linear_combination hza + hzb

end GlobalTheory.LogU
