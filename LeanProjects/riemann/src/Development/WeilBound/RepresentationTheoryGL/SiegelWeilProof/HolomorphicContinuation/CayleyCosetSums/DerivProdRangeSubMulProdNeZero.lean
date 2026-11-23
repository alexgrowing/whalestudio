import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.SingToDiffAlt

noncomputable section

open Matrix

namespace PositivityTheory.Rg.Sw.HSt

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs

variable {n : ℕ}

theorem embOn_single_pf (s : Finset (Fin n)) (a b : s) :
    embOn s (Matrix.single a b (1 : ℂ)) = Matrix.single (a : Fin n) (b : Fin n) 1 := by
  ext i j
  by_cases hi : i = (a : Fin n) <;> by_cases hj : j = (b : Fin n)
  · subst hi hj
    simp [embOn, Matrix.single_apply]
  · simp only [embOn, Matrix.single_apply, hj, and_false, if_false]
    split_ifs with h h' <;> simp_all [Subtype.ext_iff]
  · simp only [embOn, Matrix.single_apply, hi, false_and, if_false]
    split_ifs with h h' <;> simp_all [Subtype.ext_iff]
  · simp only [embOn, Matrix.single_apply, hi, false_and, if_false]
    split_ifs with h h' <;> simp_all [Subtype.ext_iff]

theorem deriv_prod_range_sub_mul_prod_ne_zero (n m : ℕ) (hmn : m < n) :
    deriv (fun z : ℂ => (∏ i ∈ Finset.range (n - m), ((i : ℂ) - z)) *
      (∏ i ∈ Finset.range (n - (n - m)), ((i : ℂ) - m - z))) 0 ≠ 0 := by
  obtain ⟨k, hk⟩ : ∃ k, n - m = k + 1 := ⟨n - m - 1, by omega⟩
  have hm : n - (n - m) = m := by omega
  rw [hm, hk]
  set C : ℂ → ℂ := fun z => ∏ i ∈ Finset.range k, (((i + 1 : ℕ) : ℂ) - z) with hCdef
  set B : ℂ → ℂ := fun z => ∏ i ∈ Finset.range m, ((i : ℂ) - m - z) with hBdef
  have hfun : (fun z : ℂ => (∏ i ∈ Finset.range (k + 1), ((i : ℂ) - z)) *
      ∏ i ∈ Finset.range m, ((i : ℂ) - m - z)) = fun z => (C z * (0 - z)) * B z := by
    funext z
    rw [Finset.prod_range_succ']
    simp [C, B]
  have hC : DifferentiableAt ℂ C 0 := DifferentiableAt.fun_finsetProd (fun i _ => by fun_prop)
  have hB : DifferentiableAt ℂ B 0 := DifferentiableAt.fun_finsetProd (fun i _ => by fun_prop)
  have key : HasDerivAt (fun z => (C z * (0 - z)) * B z) ((C 0 * (-1)) * B 0) 0 := by
    have h := (hC.hasDerivAt.mul ((hasDerivAt_id (0 : ℂ)).const_sub 0)).mul hB.hasDerivAt
    convert h using 1 <;> first | rfl | simp
  rw [hfun, key.deriv]
  have hC0 : C 0 ≠ 0 := by
    simp only [C, sub_zero]
    exact Finset.prod_ne_zero_iff.mpr (fun i _ => by exact_mod_cast Nat.succ_ne_zero i)
  have hB0 : B 0 ≠ 0 := by
    simp only [B, sub_zero]
    refine Finset.prod_ne_zero_iff.mpr (fun i hi => ?_)
    have hi' : i < m := Finset.mem_range.mp hi
    rw [sub_ne_zero]
    exact_mod_cast hi'.ne
  simp [hC0, hB0]

end PositivityTheory.Rg.Sw.HSt
