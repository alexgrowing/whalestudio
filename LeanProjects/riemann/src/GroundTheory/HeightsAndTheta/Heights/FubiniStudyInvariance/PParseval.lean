import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FubiniStudyInvariance.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open scoped ComplexConjugate
open MvPolynomial

noncomputable section

namespace FSInv

open CP

theorem Parseval.proof (hO : Orth.Statement) (hS : Sesq.Statement) (hI : InnerSelf.Statement) :
    Parseval.Statement := by
  intro N n P hP
  have hdeg : ∀ a ∈ P.support, a.degree = n := fun a ha =>
    (IsHomogeneous.degree_eq_sum_deg_support ((mem_homogeneousSubmodule _ _).mp hP) ha).symm
  have hmem : ∀ a ∈ P.support, monomial a (1 : ℂ) ∈ H0 N n := fun a ha =>
    (mem_homogeneousSubmodule _ _).mpr (isHomogeneous_monomial _ (hdeg a ha))
  have hsum : ∀ s ⊆ P.support, (∑ b ∈ s, P.coeff b • monomial b (1 : ℂ)) ∈ H0 N n := fun s hs =>
    Submodule.sum_mem _ fun b hb => Submodule.smul_mem _ _ (hmem b (hs hb))

  have hright : ∀ R ∈ H0 N n, ∀ s ⊆ P.support,
      l2Inner (N := N) n R (∑ b ∈ s, P.coeff b • monomial b (1 : ℂ)) =
        ∑ b ∈ s, P.coeff b * l2Inner n R (monomial b 1) := by
    intro R hR s
    induction s using Finset.induction_on with
    | empty => intro _; simp [l2Inner, fsPair]
    | insert b s hb ih =>
      intro hs
      have hs' : s ⊆ P.support := (Finset.subset_insert _ _).trans hs
      rw [Finset.sum_insert hb, Finset.sum_insert hb, add_comm,
        (hS N n _ _ R (hsum s hs') (hmem b (hs (Finset.mem_insert_self _ _))) hR _).2.1,
        ih hs', add_comm]

  have hleft : ∀ R ∈ H0 N n, ∀ s ⊆ P.support,
      l2Inner (N := N) n (∑ b ∈ s, P.coeff b • monomial b (1 : ℂ)) R =
        ∑ b ∈ s, conj (P.coeff b) * l2Inner n (monomial b 1) R := by
    intro R hR s
    induction s using Finset.induction_on with
    | empty => intro _; simp [l2Inner, fsPair]
    | insert b s hb ih =>
      intro hs
      have hs' : s ⊆ P.support := (Finset.subset_insert _ _).trans hs
      rw [Finset.sum_insert hb, Finset.sum_insert hb, add_comm,
        (hS N n _ _ R (hsum s hs') (hmem b (hs (Finset.mem_insert_self _ _))) hR _).1,
        ih hs', add_comm]
  have hPs : P = ∑ a ∈ P.support, P.coeff a • monomial a (1 : ℂ) := by
    conv_lhs => rw [P.as_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [smul_monomial, smul_eq_mul, mul_one]
  have hdiag : ∀ a ∈ P.support, l2Inner (N := N) n (monomial a (1 : ℂ)) (monomial a 1) =
      (((∏ i, ((a i).factorial : ℝ)) * N.factorial / (n + N).factorial : ℝ) : ℂ) := by
    intro a ha
    rw [hI, ← fubiniStudy_l2Norm_sq_eq, ← hdeg a ha, fubiniStudy_l2Norm_monomial_sq]
  have key : l2Inner (N := N) n P P = ∑ a ∈ P.support, conj (P.coeff a) * P.coeff a *
      (((∏ i, ((a i).factorial : ℝ)) * N.factorial / (n + N).factorial : ℝ) : ℂ) := by
    conv_lhs => rw [hPs]
    rw [hleft _ (hsum _ subset_rfl) _ subset_rfl]
    refine Finset.sum_congr rfl fun a ha => ?_
    rw [hright _ (hmem a ha) _ subset_rfl, Finset.mul_sum,
      Finset.sum_eq_single a, hdiag a ha, mul_assoc]
    · intro b hb hba
      have h0 : l2Inner (N := N) n (monomial a (1 : ℂ)) (monomial b 1) = 0 := by
        rw [← hdeg a ha]
        exact hO N a b (Ne.symm hba) (by rw [hdeg a ha, hdeg b hb])
      rw [h0, mul_zero, mul_zero]
    · intro ha'; exact absurd ha ha'
  rw [fubiniStudy_l2Norm_sq_eq]
  apply Complex.ofReal_injective
  rw [← hI N n P, key]
  push_cast
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Complex.conj_mul']

end FSInv

end

end GroundTheory.Heights₂.Heights
