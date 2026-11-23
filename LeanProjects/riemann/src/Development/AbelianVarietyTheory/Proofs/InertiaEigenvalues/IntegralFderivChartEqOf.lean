import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SumLieCoord
import Development.AbelianVarietyTheory.Definitions.Divisors.MeasurableCompInfGL

open NumberField MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.JSW

noncomputable section

namespace GlobalTheory.JSW

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

theorem fderiv_chart_rmul (φ : Sm E a) (g : GA E a) (y : GL (Fin a) (Cinf E)) (W : Lie E a) :
    fderiv ℝ (chart φ.1 g) (toL y.val) (rmul (toL y.val) W) =
      lieD (toL ((y⁻¹).val * Matrix.of W * y.val)) φ.1 (g * infGL E a y) := by
  rw [← chart_val (lieD _ φ.1), chart_lieD φ.2 _ g (val_mem_invSet y)]
  congr 1
  change Matrix.of W * y.val = y.val * ((y⁻¹).val * Matrix.of W * y.val)
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul]

theorem lieD_eq_sum (V : Lie E a) (F : GA E a → ℂ) (h : GA E a) :
    lieD V F h = ∑ i, (lieCoord E a i V) * lieD (lieBasis E a i) F h := by
  conv_lhs => rw [← sum_lieCoord V]
  rw [lieD, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, Complex.real_smul]
  rfl

theorem smul_fderiv_chart_comp (φ : Sm E a) (g : GA E a) (y : GL (Fin a) (Cinf E)) (c : ℂ) :
    c • (fderiv ℝ (chart φ.1 g) (toL y.val)).comp (rmul (toL y.val)) =
      ∑ p, (c * adCoef y p * (lie E a (lieBasis E a p.1) φ).1 (g * infGL E a y)) • lieCoord E a p.2 := by
  refine ContinuousLinearMap.coe_injective ((lieBasis E a).ext fun r => ?_)
  simp only [ContinuousLinearMap.coe_coe, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_sum', Finset.sum_apply, fderiv_chart_rmul, CuspRep.lie_apply]
  rw [lieD_eq_sum, Fintype.sum_prod_type, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single r]
  · simp only [lieCoord, adCoef, ContinuousLinearMap.coe_comp', Function.comp_apply, LinearMap.coe_toContinuousLinearMap',
      Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_eq_same, Complex.ofRealCLM_apply, Complex.ofReal_one,
      smul_eq_mul, mul_one]
    ring
  · intro j _ hj
    simp [lieCoord, Module.Basis.repr_self, Finsupp.single_apply, hj]
  · simp

theorem integral_fderiv_chart_eq_of {X : Type} [MeasurableSpace X] (ν : Measure X) (k : X → ℂ)
    (γ : X → GL (Fin a) (Cinf E)) (hrc : ∀ p, IsRapidInf ν (fun x => k x * adCoef (γ x) p) γ) (φ : Sm E a)
    (hb : ∀ i, ∃ C : ℝ, ∀ g, ‖(lie E a (lieBasis E a i) φ).1 g‖ ≤ C) (g : GA E a) :
    ∫ x, k x • (fderiv ℝ (chart φ.1 g) (toL (γ x).val)).comp (rmul (toL (γ x).val)) ∂ν =
      ∑ p, kerOp ν (fun x => k x * adCoef (γ x) p) γ (lie E a (lieBasis E a p.1) φ).1 g • lieCoord E a p.2 := by
  have hint : ∀ p, Integrable (fun x => (k x * adCoef (γ x) p) *
      (lie E a (lieBasis E a p.1) φ).1 (g * infGL E a (γ x))) ν := by
    intro p
    obtain ⟨C, hC⟩ := hb p.1
    exact (hrc p).integrable (lie E a (lieBasis E a p.1) φ).2 ⟨C, 0, fun y => by simpa using hC _⟩
  simp_rw [smul_fderiv_chart_comp]
  rw [integral_finset_sum _ fun p _ => (hint p).smul_const _]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [integral_smul_const]
  rfl

end GlobalTheory.JSW
