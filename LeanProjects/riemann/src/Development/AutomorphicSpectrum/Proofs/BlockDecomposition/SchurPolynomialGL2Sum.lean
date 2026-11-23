import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.RationalPrimesBelowPlaces
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CosetInd
open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open scoped NumberField.AdeleRing ValuativeRel

set_option maxSynthPendingDepth 1

namespace GlobalTheory.CompanionTheory.WS.SchurTwo

open GroundTheory.Automorphic.Spherical

theorem sum_Icc_sub_succ {G : Type*} [AddCommGroup G] (f : ℤ → G) (D A : ℤ) (h : D ≤ A) :
    ∑ j ∈ Finset.Icc D A, (f j - f (j + 1)) = f D - f (A + 1) := by
  induction A, h using Int.le_induction with
  | base => simp
  | succ A hA ih =>
    have hI : Finset.Icc D (A + 1) = insert (A + 1) (Finset.Icc D A) := by
      ext x
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    rw [hI, Finset.sum_insert (by simp), ih]
    abel

theorem alternant_two (a b : ℤ) :
    alternant ![a, b] = monomial ![a, b] - monomial ![b, a] := by
  rw [alternant_eq_det, Matrix.det_fin_two]
  simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [← monomial_add, ← monomial_add]
  congr 2
  · funext i
    fin_cases i <;> simp
  · funext i
    fin_cases i <;> simp

theorem monomial_mul_two (a b c d : ℤ) :
    (monomial ![a, b] : LaurentRing 2) * monomial ![c, d] = monomial ![a + c, b + d] := by
  rw [← monomial_add]
  congr 1
  funext i
  fin_cases i <;> simp

theorem schur_two_eq_sum (A D : ℤ) (h : D ≤ A) :
    schur ![A, D] = ∑ j ∈ Finset.Icc D A, (monomial ![A + D - j, j] : LaurentRing 2) := by
  refine mul_left_cancel₀ (alternant_staircase_ne_zero (n := 2)) ?_
  have hs : staircase 2 = ![1, 0] := by
    funext i
    fin_cases i <;> simp [staircase]
  have hl : ![A, D] + staircase 2 = ![A + 1, D] := by
    rw [hs]
    funext i
    fin_cases i <;> simp
  rw [alternant_mul_schur, hl, hs, alternant_two, alternant_two, Finset.mul_sum]
  have hterm : ∀ j ∈ Finset.Icc D A,
      ((monomial ![1, 0] : LaurentRing 2) - monomial ![0, 1]) * monomial ![A + D - j, j] =
        (fun j : ℤ => (monomial ![A + D + 1 - j, j] : LaurentRing 2)) j -
          (fun j : ℤ => (monomial ![A + D + 1 - j, j] : LaurentRing 2)) (j + 1) := by
    intro j _
    rw [sub_mul, monomial_mul_two, monomial_mul_two]
    have e1 : (1 : ℤ) + (A + D - j) = A + D + 1 - j := by ring
    have e2 : (0 : ℤ) + j = j := by ring
    have e3 : (0 : ℤ) + (A + D - j) = A + D + 1 - (j + 1) := by ring
    have e4 : (1 : ℤ) + j = j + 1 := by ring
    rw [e1, e2, e3, e4]
  rw [Finset.sum_congr rfl hterm, sum_Icc_sub_succ _ D A h]
  have e5 : A + D + 1 - D = A + 1 := by ring
  have e6 : A + D + 1 - (A + 1) = D := by ring
  simp only [e5, e6]

theorem evalAt_monomial_two (x y : ℂˣ) (a b : ℤ) :
    evalAt ![x, y] (monomial ![a, b]) = (x : ℂ) ^ a * (y : ℂ) ^ b := by
  rw [evalAt_single, one_mul, monomialChar_apply, Fin.prod_univ_two]
  simp [Units.val_zpow_eq_zpow_val]

theorem evalAt_schur_two :
    ∀ (x y : ℂˣ) (A D : ℤ), D ≤ A → Spherical.evalAt ![x, y] (Spherical.schur ![A, D]) = ∑ j ∈ Finset.Icc D A, (x : ℂ) ^ (A + D - j) * (y : ℂ) ^ j := by
  intro x y A D h
  rw [schur_two_eq_sum A D h, map_sum]
  exact Finset.sum_congr rfl fun j _ => evalAt_monomial_two x y _ _

end GlobalTheory.CompanionTheory.WS.SchurTwo
