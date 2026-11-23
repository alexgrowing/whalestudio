import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.PeriodValuationTheory
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.WtSubOneLe
import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetFactorDepthInChartIndependentClosedField

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.DepthDegree

open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh GlobalTheory.FGDepth GlobalTheory.LawLog GlobalTheory.FactorDepth GlobalTheory.DepthField

variable {C : Type} [Field C]

theorem le_order_subst_monomial {σ τ : Type} {E : σ → MvPowerSeries τ C} (hE : HasSubst E)
    (h0 : ∀ s, constantCoeff (E s) = 0) (β : σ →₀ ℕ) :
    (((Finsupp.degree β : ℕ)) : ℕ∞) ≤ (subst E (monomial β (1 : C))).order := by
  classical
  rw [subst_monomial hE, map_one, one_mul, Finsupp.prod]
  refine le_trans ?_ (le_order_prod _ _)
  rw [show ((β.degree : ℕ) : ℕ∞) = ∑ s ∈ β.support, ((β s : ℕ) : ℕ∞) by
    rw [Finsupp.degree_apply, Nat.cast_sum]]
  exact Finset.sum_le_sum fun s _ => le_order_pow_of_constantCoeff_eq_zero _ (h0 s)

theorem derivAt0_eq_zero_of_lt_order {σ : Type} (P : MvPolynomial σ C) (g : MvPowerSeries σ C)
    (h : (P.totalDegree : ℕ∞) < g.order) : derivAt0 P g = 0 := by
  refine Finset.sum_eq_zero fun α hα => ?_
  have h1 : (((Finsupp.degree α : ℕ)) : ℕ∞) < g.order := by
    refine lt_of_le_of_lt ?_ h
    exact_mod_cast (MvPolynomial.le_totalDegree hα)
  rw [coeff_of_lt_order h1, mul_zero]

theorem depth_eq_iInf_monomial_degree_le : ∀ (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (κ : Type) [Fintype κ] [DecidableEq κ] (d : κ → ℕ) (G : ∀ b, LogFGL v (d b)) (ι : κ → Type) [∀ b, Fintype (ι b)] [∀ b, DecidableEq (ι b)] (u : ∀ b, ι b → Fin (d b) → C) (P : MvPolynomial (Σ b, ι b) C), depth G u P = ⨅ β ∈ {β : (Σ b, Fin (d b)) →₀ ℕ | β.degree ≤ P.totalDegree}, toE (v (derivAt0 P (subst (expAlong G u) (monomial β (1 : C))))) := by
  intro C _ _ v κ _ _ d G ι _ _ u P
  rw [depth_eq_iInf_monomial]
  refine le_antisymm (le_iInf₂ fun β _ => iInf_le _ β) (le_iInf fun β => ?_)
  by_cases hβ : β.degree ≤ P.totalDegree
  · exact iInf₂_le β hβ
  · have h0 : ∀ x, constantCoeff (expAlong G u x) = 0 := fun x =>
      constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero (hasSubst_lin u x.1)) (hasSubst_lin u x.1)
        ((isExp_expOf (G x.1)).1 x.2)
    have hz := derivAt0_eq_zero_of_lt_order P _ (lt_of_lt_of_le (by exact_mod_cast not_le.1 hβ)
      (le_order_subst_monomial (hasSubst_expAlong G u) h0 β))
    rw [hz, v.map_zero]
    exact le_top

end GlobalTheory.DepthDegree
