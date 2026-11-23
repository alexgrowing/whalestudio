import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsTypeIsRealConst
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChernPolyTopDensityCompHolomorphicNormSqDet
open Set Matrix Filter Topology
open GlobalTheory.HermFrame GlobalTheory.CxForm
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.GoodMetric (coordVec chernPoly curvPoly)
open scoped ContDiff ComplexOrder

namespace GlobalTheory.CxForm

theorem coe_aeval_sym_substAlg {n : ℕ} (φ : V n → V n) (v : V n) (p : MvPolynomial (Fin n × Fin n) ℂ) :
    ((MvPolynomial.aeval sym (GlobalTheory.ChernPull.substAlg (GlobalTheory.ChernPull.jac φ v) p) : Ev n) : Alt n) =
      pull (fderiv ℂ φ v) ((MvPolynomial.aeval sym p : Ev n) : Alt n) := by
  have h : ((Subalgebra.center ℂ (Alt n)).val.comp ((MvPolynomial.aeval sym).comp
      (GlobalTheory.ChernPull.substAlg (GlobalTheory.ChernPull.jac φ v)))) =
      (pull (fderiv ℂ φ v)).comp ((Subalgebra.center ℂ (Alt n)).val.comp (MvPolynomial.aeval sym)) := by
    refine MvPolynomial.algHom_ext fun x => ?_
    simp only [AlgHom.comp_apply, GlobalTheory.ChernPull.substAlg, MvPolynomial.aeval_X, map_sum, map_mul,
      MvPolynomial.aeval_C, Subalgebra.coe_val, sym, (pull_dz _ _).1, (pull_dz _ _).2, Finset.sum_mul_sum,
      smul_mul_smul_comm, GlobalTheory.ChernPull.jac]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [Subalgebra.coe_algebraMap, Subalgebra.coe_algebraMap, ← map_mul, ← Algebra.smul_def]
  exact DFunLike.congr_fun h p

theorem chernAt_comp : ∀ {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] (H : V n → Matrix r r ℂ) (φ : V n → V n) (v : V n), AnalyticAt ℂ φ v → MContDiffAt 2 H (φ v) → IsUnit (H (φ v)).det → ∀ j, (chernAt (fun w => H (φ w)) v j : Alt n) = pull (fderiv ℂ φ v) (chernAt H (φ v) j : Alt n) := by
  intro n r _ _ H φ v hφ h2 hu j
  rw [chernAt, chernAt, GlobalTheory.ChernPull.chernPoly_comp hφ h2 hu, Subalgebra.coe_smul, Subalgebra.coe_smul, map_smul,
    coe_aeval_sym_substAlg]

end GlobalTheory.CxForm
