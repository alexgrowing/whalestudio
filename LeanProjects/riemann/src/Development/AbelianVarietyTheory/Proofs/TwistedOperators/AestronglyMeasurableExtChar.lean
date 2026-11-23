import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DetUnitScalarMul
open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S GlobalTheory.OpTrace GlobalTheory.HCChar GlobalTheory.SUChar
open GlobalTheory.Orb (ujMat ujRep CcMat IsCharFn IsRegSS)
open GlobalTheory.DSSU (SUJ SUset Ext)
open GlobalTheory.SqIntSU (scalarMul circleHaar)

noncomputable section

namespace GlobalTheory.ExtChar

attribute [local instance] GlobalTheory.SqIntSU.circleBorelMS GlobalTheory.SqIntSU.circleBorelSpace GlobalTheory.SqIntSU.circleHaar_isHaar
  GlobalTheory.SqIntSU.circleHaar_finite GlobalTheory.SqIntSU.locallyCompact_special GlobalTheory.SqIntSU.secondCountable_special
  GlobalTheory.SqIntSU.sigmaCompact_special GlobalTheory.DSSU.borelSpace_SUJ

variable {n : ℕ} (ε : Fin n → Bool)

theorem measurable_detRoot : Measurable (detRoot (n := n) ε) := by
  have hdet : Continuous fun x : UJ ε => (umat x).det :=
    (Units.continuous_val.comp continuous_subtype_val).matrix_det
  have h1 : Measurable fun x : UJ ε => Complex.arg (umat x).det / (n : ℝ) :=
    (Complex.measurable_arg.comp hdet.measurable).div_const _
  exact Circle.exp.continuous.measurable.comp h1

variable [NeZero n]

theorem measurable_root (j : ZMod n) : Measurable fun x : UJ ε => root ε x j :=
  (measurable_detRoot ε).mul_const _

theorem measurable_part (j : ZMod n) : Measurable fun x : UJ ε => part ε x j := by
  have hc : Continuous fun p : Circle × UJ ε =>
      GlobalTheory.SqIntSU.unitScalar ε (p.1 * ZMod.toCircle j)⁻¹ * p.2 :=
    ((GlobalTheory.SqIntSU.continuous_unitScalar ε).comp ((continuous_fst.mul continuous_const).inv)).mul continuous_snd
  have hp : Measurable fun x : UJ ε => (detRoot ε x, x) := (measurable_detRoot ε).prodMk measurable_id
  have hcomp : Measurable ((fun p : Circle × UJ ε =>
      GlobalTheory.SqIntSU.unitScalar ε (p.1 * ZMod.toCircle j)⁻¹ * p.2) ∘ fun x : UJ ε => (detRoot ε x, x)) :=
    hc.measurable.comp hp
  have he : (fun x : UJ ε => GlobalTheory.SqIntSU.unitScalar ε (root ε x j)⁻¹ * x) = ((fun p : Circle × UJ ε =>
      GlobalTheory.SqIntSU.unitScalar ε (p.1 * ZMod.toCircle j)⁻¹ * p.2) ∘ fun x : UJ ε => (detRoot ε x, x)) := by
    funext x; simp only [Function.comp_apply, root]
  have hm : Measurable fun x : UJ ε => GlobalTheory.SqIntSU.unitScalar ε (root ε x j)⁻¹ * x := he ▸ hcomp
  exact hm.subtype_mk

theorem measurable_extChar (m : ℤ) (Θ : SUJ ε → ℂ) (hΘ : Measurable Θ) : Measurable (extChar ε m Θ) := by
  have hz : Continuous fun z : Circle => (z : ℂ) ^ m :=
    Continuous.zpow₀ (by fun_prop) m (fun z => Or.inl (Circle.coe_ne_zero z))
  unfold extChar
  refine Measurable.const_mul ?_ _
  refine Finset.measurable_sum _ fun j _ => ?_
  exact (hz.measurable.comp (measurable_root ε j)).mul (hΘ.comp (measurable_part ε j))

end GlobalTheory.ExtChar

namespace GlobalTheory.ExtChar

attribute [local instance] GlobalTheory.SqIntSU.circleBorelMS GlobalTheory.SqIntSU.circleBorelSpace GlobalTheory.SqIntSU.circleHaar_isHaar
  GlobalTheory.SqIntSU.circleHaar_finite GlobalTheory.SqIntSU.locallyCompact_special GlobalTheory.SqIntSU.secondCountable_special
  GlobalTheory.SqIntSU.sigmaCompact_special GlobalTheory.DSSU.borelSpace_SUJ

theorem aestronglyMeasurable_extChar : ∀ (n : ℕ) [NeZero n] (ε : Fin n → Bool) (μ' : Measure (SUJ ε)) [μ'.IsHaarMeasure] (m : ℤ) (Θ' : SUJ ε → ℂ), AEStronglyMeasurable Θ' μ' → AEStronglyMeasurable (GlobalTheory.ExtChar.extChar ε m Θ') (letI := GlobalTheory.SqIntSU.circleBorelMS; Measure.map (scalarMul ε) (circleHaar.prod μ')) := by
  intro n _ ε μ' _ m Θ' hΘ
  have hm'' : Measurable (hΘ.mk Θ') := hΘ.stronglyMeasurable_mk.measurable
  have hae : ∀ᵐ g ∂μ', Θ' g = hΘ.mk Θ' g := hΘ.ae_eq_mk
  obtain ⟨N, hsub, hNm, hN0⟩ := exists_measurable_superset_of_null (ae_iff.1 hae)
  have hE : MeasurableSet (⋃ j : ZMod n, (fun x => part ε x j) ⁻¹' N) :=
    MeasurableSet.iUnion fun j => measurable_part ε j hNm
  have hpre : scalarMul ε ⁻¹' (⋃ j : ZMod n, (fun x => part ε x j) ⁻¹' N) ⊆
      ⋃ k : ZMod n, Set.univ ×ˢ ((fun g => cen ε k * g) ⁻¹' N) := by
    rintro ⟨z, g⟩ hx
    obtain ⟨j, hj⟩ := Set.mem_iUnion.1 hx
    obtain ⟨i, hi⟩ := root_scalarMul ε z g
    refine Set.mem_iUnion.2 ⟨i + j, Set.mem_univ _, ?_⟩
    have h := part_scalarMul ε z g i hi j
    simp only [Set.mem_preimage] at hj ⊢
    rw [h] at hj
    exact hj
  have hE0 : Measure.map (scalarMul ε) (circleHaar.prod μ') (⋃ j : ZMod n, (fun x => part ε x j) ⁻¹' N) = 0 := by
    rw [Measure.map_apply (GlobalTheory.SqIntSU.continuous_scalarMul ε).measurable hE]
    refine measure_mono_null hpre (measure_iUnion_null fun k => ?_)
    rw [Measure.prod_prod, measure_preimage_mul, hN0, mul_zero]
  have heq : extChar ε m (hΘ.mk Θ') =ᵐ[Measure.map (scalarMul ε) (circleHaar.prod μ')] extChar ε m Θ' := by
    refine ae_iff.2 (measure_mono_null (fun x hx => ?_) hE0)
    by_contra hxE
    apply hx
    simp only [Set.mem_iUnion, Set.mem_preimage, not_exists] at hxE
    simp only [extChar]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    have h : Θ' (part ε x j) = hΘ.mk Θ' (part ε x j) := by
      by_contra h
      exact hxE j (hsub h)
    rw [h]
  exact (measurable_extChar ε m _ hm'').aestronglyMeasurable.congr heq

end GlobalTheory.ExtChar
