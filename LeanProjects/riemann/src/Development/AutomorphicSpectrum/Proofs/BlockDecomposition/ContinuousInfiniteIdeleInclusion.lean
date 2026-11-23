import Mathlib
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.UnitTestFunctions.LiftUnit
import GroundTheory.GlobalFields.TateThesis.GlobalZetaInfinite

noncomputable section

open NumberField NumberField.mixedEmbedding IsDedekindDomain Matrix MeasureTheory Filter Topology
open scoped NumberField.AdeleRing SchwartzMap Classical

set_option synthInstance.maxSize 1000

namespace GlobalTheory.CompanionTheory.EisTestFun

open GroundTheory.Global GroundTheory.Automorphic GroundTheory.Global.IdeleGroup PositivityTheory.RgEis PositivityTheory.RgEis.TF

variable {k : Type} [Field k] [NumberField k]

theorem continuous_infinite_idele_inclusion :
    Continuous (ofInfinite : (InfiniteAdeleRing k)ˣ → IdeleGroup k) :=
  (ContinuousMulEquiv.symm (prodEquiv k)).continuous.comp (Continuous.prodMk_left 1)

theorem ideleModule_ofInfinite_eq (a : (InfiniteAdeleRing k)ˣ) :
    (ideleModule k (ofInfinite a) : ℝ) = ∏ w : InfinitePlace k, ‖(a : InfiniteAdeleRing k) w‖ ^ w.mult := by
  have h1 : ∀ w, ((ofInfinite a : IdeleGroup k) : 𝔸[k]).1 w = (a : InfiniteAdeleRing k) w := fun w => by
    have := congrArg (fun u : (InfiniteAdeleRing k)ˣ => (u : InfiniteAdeleRing k) w) (toInfinite_ofInfinite a)
    exact this
  have h2 : ∀ v, ((ofInfinite a : IdeleGroup k) : 𝔸[k]).2 v = 1 := fun v => by
    have := congrArg (fun u : (FiniteAdeleRing (𝓞 k) k)ˣ => (u : FiniteAdeleRing (𝓞 k) k) v) (toFinite_ofInfinite a)
    exact this
  rw [ideleModule_eq]
  simp only [h1, h2, norm_one, finprod_one, mul_one]

theorem exists_norm_rd_le (φ : 𝓢(Unit → mixedSpace k, ℂ)) (K : ℕ) :
    ∃ C, 0 ≤ C ∧ ∀ x : InfiniteAdeleRing k,
      ‖rd φ (fun _ => x)‖ ≤ C * ∏ w, ((1 + ‖x w‖) ^ K)⁻¹ := by
  let e : mixedSpace k ≃L[ℝ] (Unit → mixedSpace k) :=
    (ContinuousLinearEquiv.funUnique Unit ℝ (mixedSpace k)).symm
  obtain ⟨C, hC, h⟩ := exists_norm_schwartz_le_prod (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e φ) K
  refine ⟨C, hC, fun x => ?_⟩
  have hx := h x
  have he : (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e φ) (homeomorphMixedSpace k x) =
      rd φ (fun _ => x) := by
    simp only [SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp, rd]
    congr 1
  rwa [he] at hx

theorem module_rpow_eq (a : (InfiniteAdeleRing k)ˣ) (x : ℝ) :
    (ideleModule k (ofInfinite a) : ℝ) ^ x =
      ∏ w : InfinitePlace k, ‖(a : InfiniteAdeleRing k) w‖ ^ ((w.mult : ℝ) * x) := by
  rw [ideleModule_ofInfinite_eq, ← Real.finset_prod_rpow _ _ (fun w _ => by positivity)]
  refine Finset.prod_congr rfl fun w _ => ?_
  rw [Real.rpow_mul (norm_nonneg _), Real.rpow_natCast]

theorem integrable_norm_rd_mul (φ : 𝓢(Unit → mixedSpace k, ℂ)) {x : ℝ} (hx : 1 < x)
    (hc : Continuous fun a : (InfiniteAdeleRing k)ˣ =>
      ‖rd φ (fun _ => (a : InfiniteAdeleRing k))‖ * (ideleModule k (ofInfinite a) : ℝ) ^ x) :
    Integrable (fun a : (InfiniteAdeleRing k)ˣ =>
      ‖rd φ (fun _ => (a : InfiniteAdeleRing k))‖ * (ideleModule k (ofInfinite a) : ℝ) ^ x)
      (infiniteIdeleMeasure k) := by
  obtain ⟨K, hK⟩ := exists_nat_gt (2 * x + 2)
  obtain ⟨C, hC, h⟩ := exists_norm_rd_le φ K
  refine Integrable.mono' ((integrable_infiniteZetaBound (K := k) hx.le hK).const_mul C)
    hc.aestronglyMeasurable (Eventually.of_forall fun a => ?_)
  have hm : 0 ≤ (ideleModule k (ofInfinite a) : ℝ) ^ x := Real.rpow_nonneg (ideleModule k (ofInfinite a)).2.le _
  rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) hm)]
  calc ‖rd φ (fun _ => (a : InfiniteAdeleRing k))‖ * (ideleModule k (ofInfinite a) : ℝ) ^ x
      ≤ (C * ∏ w, ((1 + ‖(a : InfiniteAdeleRing k) w‖) ^ K)⁻¹) * (ideleModule k (ofInfinite a) : ℝ) ^ x :=
        mul_le_mul_of_nonneg_right (h a) hm
    _ = C * infiniteZetaBound x K a := by
        rw [module_rpow_eq, infiniteZetaBound, mul_assoc, ← Finset.prod_mul_distrib]
        congr 1
        refine Finset.prod_congr rfl fun w _ => ?_
        rw [div_eq_mul_inv, mul_comm]

theorem zInf_ne_zero : ZInf := by
  intro k _ _ φ ω h h1 x hx
  have hc0 : Continuous fun a : (InfiniteAdeleRing k)ˣ => rd φ (fun _ => (a : InfiniteAdeleRing k)) :=
    φ.continuous.comp (continuous_pi fun _ =>
      (homeomorphMixedSpace k).continuous.comp Units.continuous_val)
  have hm0 : Continuous fun a : (InfiniteAdeleRing k)ˣ => (ideleModule k (ofInfinite a) : ℝ) :=
    continuous_subtype_val.comp (IdeleGroup.continuous_ideleModule.comp continuous_infinite_idele_inclusion)
  set f : (InfiniteAdeleRing k)ˣ → ℝ := fun a =>
    ‖rd φ (fun _ => (a : InfiniteAdeleRing k))‖ * (ideleModule k (ofInfinite a) : ℝ) ^ x with hf
  have hcf : Continuous f :=
    hc0.norm.mul (hm0.rpow_const fun _ => Or.inr (by linarith))
  have hint : Integrable f (infiniteIdeleMeasure k) := integrable_norm_rd_mul φ hx hcf
  have hnn : 0 ≤ f := fun a => mul_nonneg (norm_nonneg _)
    (Real.rpow_nonneg (ideleModule k (ofInfinite a)).2.le _)
  have hpt : ∀ a : (InfiniteAdeleRing k)ˣ,
      rd φ (fun _ => (a : InfiniteAdeleRing k)) * (ω.toIdele (ofInfinite a) : ℂ) *
        ((ideleModule k (ofInfinite a) : ℝ) : ℂ) ^ (x : ℂ) = ((f a : ℝ) : ℂ) := fun a => by
    obtain ⟨r, hr, e⟩ := h a
    have hn : r = ‖rd φ (fun _ => (a : InfiniteAdeleRing k))‖ := by
      have := congrArg norm e
      rw [norm_mul, Circle.norm_coe, mul_one, Complex.norm_real, Real.norm_of_nonneg hr] at this
      exact this.symm
    rw [e, hn, hf]
    push_cast
    rw [Complex.ofReal_cpow (ideleModule k (ofInfinite a)).2.le]
  have hz : zInf φ ω x = ((∫ a, f a ∂infiniteIdeleMeasure k : ℝ) : ℂ) := by
    rw [zInf, ← integral_complex_ofReal]
    exact integral_congr_ae (Eventually.of_forall hpt)
  have hpos : 0 < ∫ a, f a ∂infiniteIdeleMeasure k := by
    rw [integral_pos_iff_support_of_nonneg hnn hint]
    have hop : IsOpen (Function.support f) := isOpen_compl_singleton.preimage hcf
    refine hop.measure_pos _ ⟨1, ?_⟩
    have hm1 : 0 < (ideleModule k (ofInfinite (1 : (InfiniteAdeleRing k)ˣ)) : ℝ) ^ x :=
      Real.rpow_pos_of_pos (ideleModule k (ofInfinite _)).2 _
    have : f 1 ≠ 0 := by
      simp only [hf, Units.val_one]
      exact mul_ne_zero (norm_ne_zero_iff.2 h1) hm1.ne'
    exact this
  rw [hz]
  exact_mod_cast hpos.ne'

end GlobalTheory.CompanionTheory.EisTestFun
