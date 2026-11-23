import Formalism.ThetaLogCoordinates.TraceIsometryWeights.SchurTraceProofs.WeightCompApply
import Formalism.ThetaLogCoordinates.TraceIsometryWeights.SchurTraceProofs.FischerAdjointnessHolds

namespace Formalism.InvariantFactorPaths.PW

open Formalism.GM.M Formalism.GM.DimensionMonotonicity MvPolynomial Finset

variable {p : ℕ} [Fact p.Prime]

theorem mem_intPol_addSubgroup {σ : Type} (x : MvPolynomial σ ℚ_[p]) :
    x ∈ (IntPol p σ).toAddSubgroup ↔ ∀ m, ‖x.coeff m‖ ≤ 1 := by
  rw [Submodule.mem_toAddSubgroup, intPol_iff_norm]

theorem intPol_zpClosed (σ : Type) : ZpClosed p (IntPol p σ).toAddSubgroup := by
  intro c hc x hx
  rw [mem_intPol_addSubgroup] at hx ⊢
  intro m
  rw [coeff_smul, smul_eq_mul, norm_mul]
  exact mul_le_one₀ hc (norm_nonneg _) (hx m)

theorem intPol_whc {σ M : Type} [AddCommMonoid M] (w : σ → M) (μ : M) (x : MvPolynomial σ ℚ_[p])
    (hx : x ∈ (IntPol p σ).toAddSubgroup) :
    weightedHomogeneousComponent w μ x ∈ (IntPol p σ).toAddSubgroup := by
  classical
  rw [mem_intPol_addSubgroup] at hx ⊢
  intro m
  rw [coeff_weightedHomogeneousComponent]
  split_ifs
  · exact hx m
  · rw [norm_zero]; exact zero_le_one

theorem polLatData_of (hB : LatBasisPol) {p : ℕ} [Fact p.Prime] {N r n : ℕ} (LL L2 : Letters N) (j : ℕ)
    (e : Fin n ↪o Fin r) :
    LatData p (GAe p LL j e) (Pol p r L2) (IntPol p (Fin N × Fin r)).toAddSubgroup L2.total where
  stable := GAe_pol_stable LL L2 j e
  fd := pol_fd L2
  finW := GAe_pol_finW LL L2 j e
  bound := GAe_pol_bound LL L2 j e
  closed := intPol_zpClosed _
  div := fun a b hab k x hx =>
    divided_integral_holds p N r LL j (e a) (e b) (fun h => hab (e.injective h)) k x hx
  graded := fun μ x hx => intPol_whc _ μ x hx
  basis := fun U hU => by
    have := pol_fd (p := p) (r := r) L2
    exact hB p _ U (Submodule.finiteDimensional_of_le hU)

end Formalism.InvariantFactorPaths.PW
