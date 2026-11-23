import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.CurvePt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1

universe u v w

section

variable {K : Type u} [Fintype K] {ι : K → Type v} [∀ k, Fintype (ι k)] {F : Type w} [Field F]
  [DecidableEq K]

attribute [local instance] MvPolynomial.weightedGradedAlgebra

theorem ChartFiniteIrrel.weighted_le_pow (t : ℕ) :
    weightedHomogeneousSubmodule F (mw (ι := ι)) (fun _ => t) ≤
      ((Ideal.span (weightedHomogeneousSubmodule F (mw (ι := ι)) (fun _ => 1) : Set (MRingOver F ι))) ^
        t).restrictScalars F := by
  classical
  induction t with
  | zero => simp
  | succ t ih =>
    rw [weightedHomogeneousSubmodule_eq_finsupp_supported, AddMonoidAlgebra.supported_eq_span_single,
      Submodule.span_le]
    rintro _ ⟨m, hm, rfl⟩
    have hm' : ∀ k, ∑ i, m ⟨k, i⟩ = t + 1 := fun k => congrFun ((weight_mw m).symm.trans hm) k
    have hj : ∀ k, ∃ i, m ⟨k, i⟩ ≠ 0 := fun k => by
      obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero (s := Finset.univ)
        (f := fun i => m ⟨k, i⟩) (by rw [hm' k]; omega)
      exact ⟨i, hi⟩
    choose j hj using hj
    let d : (Σ k, ι k) →₀ ℕ := Finsupp.equivFunOnFinite.symm fun p => if p.2 = j p.1 then 1 else 0
    have hd : ∀ k i, d ⟨k, i⟩ = if i = j k then 1 else 0 := fun k i => rfl
    have hdm : d ≤ m := Finsupp.le_def.mpr fun ⟨k, i⟩ => by
      rw [hd]
      split_ifs with h
      · subst h; exact Nat.one_le_iff_ne_zero.mpr (hj k)
      · exact Nat.zero_le _
    have h1 : ∀ k, ∑ i, d ⟨k, i⟩ = 1 := fun k => by simp [hd]
    have hsum : ∀ k, ∑ i, (m - d) ⟨k, i⟩ = t := fun k => by
      have h2 : ∑ i, ((m - d) ⟨k, i⟩ + d ⟨k, i⟩) = t + 1 := by
        rw [← hm' k]
        exact Finset.sum_congr rfl fun i _ => by
          rw [Finsupp.tsub_apply]; exact Nat.sub_add_cancel (Finsupp.le_def.mp hdm _)
      rw [Finset.sum_add_distrib, h1] at h2; omega
    have hmd := monomial_mem_weighted (F := F) (m - d) 1
    rw [show (fun k => ∑ i, (m - d) ⟨k, i⟩) = fun _ => t from funext hsum] at hmd
    have hd1 := monomial_mem_weighted (F := F) d 1
    rw [show (fun k => ∑ i, d ⟨k, i⟩) = fun _ => 1 from funext h1] at hd1
    show AddMonoidAlgebra.single m (1 : F) ∈ _
    rw [single_eq_monomial, ← tsub_add_cancel_of_le hdm, ← one_mul (1 : F), ← monomial_mul, pow_succ]
    exact Ideal.mul_mem_mul (ih hmd) (Ideal.subset_span hd1)

end

end GroundTheory.Heights₂.Heights.Targets
