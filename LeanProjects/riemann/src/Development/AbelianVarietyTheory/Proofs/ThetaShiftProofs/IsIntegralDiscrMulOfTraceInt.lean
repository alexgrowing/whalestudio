import Mathlib
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsThetaL2NormSquared
import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames
open scoped LaurentSeries

namespace GlobalTheory.ArcQ

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField in
open scoped LaurentSeries in

theorem _root_.GlobalTheory.ArcQ.pairE_properties : ∀ (E : Type) [Field E] [NumberField E] (X : Type) [AddCommGroup X] [Module (𝓞 E) X] (ξ : Module.Dual ℤ X), (∀ (a : 𝓞 E) x, _root_.GlobalTheory.ArcQ.pairE ξ (a • x) = (a : E) * _root_.GlobalTheory.ArcQ.pairE ξ x) ∧ (∀ x y, _root_.GlobalTheory.ArcQ.pairE ξ (x + y) = _root_.GlobalTheory.ArcQ.pairE (E := E) ξ x + _root_.GlobalTheory.ArcQ.pairE ξ y) ∧ (∀ x, Algebra.trace ℚ E (_root_.GlobalTheory.ArcQ.pairE ξ x) = ξ x) ∧ (∀ x, IsIntegral ℤ ((NumberField.discr E : E) * _root_.GlobalTheory.ArcQ.pairE ξ x)) ∧ ∀ (K : Type) [Field K] (τK : E →+* K) x, _root_.GlobalTheory.ArcQ.xiVal τK ξ x = τK (_root_.GlobalTheory.ArcQ.pairE ξ x) := by
  intro E _ _ X _ _ ξ
  classical
  set b := RingOfIntegers.basis E with hbdef
  have hB := traceForm_nondegenerate ℚ E
  set d := (Algebra.traceForm ℚ E).dualBasis hB (integralBasis E) with hd
  have hP : ∀ x, _root_.GlobalTheory.ArcQ.pairE ξ x = ∑ i, d i * (ξ (b i • x) : E) := fun x => rfl
  have hexp : ∀ y : 𝓞 E, algebraMap (𝓞 E) E y = ∑ k, (b.repr y k : E) * integralBasis E k := by
    intro y
    conv_lhs => rw [← b.sum_repr y]
    simp [integralBasis_apply, zsmul_eq_mul, b]
  have hdual : ∀ i k, Algebra.trace ℚ E (d i * integralBasis E k) = if k = i then 1 else 0 := by
    intro i k
    rw [← Algebra.traceForm_apply]
    exact LinearMap.BilinForm.apply_dualBasis_left hB _ i k
  have hL : ∀ (y : 𝓞 E) i, Algebra.trace ℚ E (d i * algebraMap (𝓞 E) E y) = (b.repr y i : ℚ) := by
    intro y i
    have e : ∀ k, d i * ((b.repr y k : E) * integralBasis E k) =
        (b.repr y k : ℚ) • (d i * integralBasis E k) := by
      intro k
      rw [Algebra.smul_def]
      simp only [eq_ratCast, Rat.cast_intCast]
      ring
    rw [hexp y, Finset.mul_sum, map_sum]
    simp_rw [e, map_smul, hdual, smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, if_true]
  have hC : ∀ x (y : 𝓞 E), Algebra.trace ℚ E (_root_.GlobalTheory.ArcQ.pairE ξ x * algebraMap (𝓞 E) E y) =
      (ξ (y • x) : ℚ) := by
    intro x y
    have e : ∀ i, d i * (ξ (b i • x) : E) * algebraMap (𝓞 E) E y =
        (ξ (b i • x) : ℚ) • (d i * algebraMap (𝓞 E) E y) := by
      intro i
      rw [Algebra.smul_def]
      simp only [eq_ratCast, Rat.cast_intCast]
      ring
    rw [hP, Finset.sum_mul, map_sum]
    simp_rw [e, map_smul, hL, smul_eq_mul]
    conv_rhs => rw [← b.sum_repr y]
    simp only [Finset.sum_smul, map_sum, smul_assoc, map_zsmul, smul_eq_mul, Int.cast_sum,
      Int.cast_mul]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have huniq : ∀ y y' : E, (∀ k, Algebra.trace ℚ E (y * integralBasis E k) =
      Algebra.trace ℚ E (y' * integralBasis E k)) → y = y' := by
    intro y y' h
    rw [← d.sum_repr y, ← d.sum_repr y']
    simp_rw [hd, LinearMap.BilinForm.dualBasis_repr_apply, Algebra.traceForm_apply, h]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro a x
    apply huniq
    intro k
    have e : (a : E) * _root_.GlobalTheory.ArcQ.pairE ξ x * integralBasis E k =
        _root_.GlobalTheory.ArcQ.pairE ξ x * algebraMap (𝓞 E) E (b k * a) := by
      rw [integralBasis_apply, map_mul]
      show (algebraMap (𝓞 E) E a) * _ * _ = _
      ring
    rw [e, hC, integralBasis_apply, hC, mul_smul]
  · intro x y
    simp only [hP, smul_add, map_add, Int.cast_add, mul_add, Finset.sum_add_distrib]
  · intro x
    have := hC x 1
    simpa using this
  · intro x
    rw [hP, Finset.mul_sum]
    refine IsIntegral.sum _ fun i _ => ?_
    have hdi : IsIntegral ℤ ((NumberField.discr E : E) * d i) := by
      have h := isIntegral_discr_mul_of_mem_traceDual (A := ℤ) (K := ℚ) (L := E) (B := 𝓞 E)
        (1 : Submodule (𝓞 E) E) (b := integralBasis E)
        (fun k => by rw [integralBasis_apply]; exact RingOfIntegers.isIntegral_coe _)
        (a := 1) (x := d i) (Submodule.one_le.1 le_rfl) (by
          rw [Submodule.mem_traceDual]
          intro a ha
          obtain ⟨y, rfl⟩ := Submodule.mem_one.1 ha
          rw [Algebra.traceForm_apply, hL]
          exact ⟨b.repr y i, rfl⟩)
      rw [← coe_discr, Algebra.smul_def, mul_one] at h
      simpa using h
    have hξ : IsIntegral ℤ ((ξ (b i • x) : ℤ) : E) := by
      simpa using (isIntegral_algebraMap (R := ℤ) (A := E) (x := ξ (b i • x)))
    rw [← mul_assoc]
    exact hdi.mul hξ
  · intro K _ τK x
    show ∑ i, τK (d i) * (ξ (b i • x) : K) = τK (_root_.GlobalTheory.ArcQ.pairE ξ x)
    rw [hP]
    simp [map_sum, map_mul, map_intCast]

end GlobalTheory.ArcQ
