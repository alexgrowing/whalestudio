import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.CuspidalMultiplicityOneTotallyComplex
import GroundTheory.AutomorphicForms.DixmierMalliavinBasic

open MeasureTheory NumberField GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C Polynomial Topology

theorem UpperTheory.norm_exp_smul_sub_le_norm_derivOp :
    ∀ (𝔸 : Type) [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸] (G : Subgroup 𝔸ˣ) (𝔤 : Submodule ℝ 𝔸) (h : IsExpLieAlgebra G 𝔤) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (π : BanachRep G E) (v : E) (X : 𝔤), (∀ g w, ‖π g w‖ = ‖w‖) → h.IsSmoothVector π v → ‖π (h.expG X) v - v‖ ≤ ‖h.derivOp π X v‖ := by
  intro 𝔸 _ _ _ _ G 𝔤 h E _ _ π v X hπ hv
  have hd : ∀ t : ℝ, HasDerivAt (fun s : ℝ => π (h.expG (s • X)) v)
      (π (h.expG (t • X)) (h.derivOp π X v)) t := by
    intro t
    have h2 := ((π (h.expG (t • X))).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ)
      (h.hasDerivAt_derivOp π hv X)
    have h3 : HasDerivAt (fun s : ℝ => π (h.expG ((t + s) • X)) v)
        (π (h.expG (t • X)) (h.derivOp π X v)) (t - t) := by
      rw [sub_self]
      refine h2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)
      simp only [Function.comp_apply, ContinuousLinearMap.coe_restrictScalars']
      rw [h.expG_add_smul, BanachRep.map_mul_apply]
    have h4 := h3.comp_sub_const t t
    simpa only [add_sub_cancel] using h4
  have hm := norm_image_sub_le_of_norm_deriv_le_segment_01'
    (f := fun s : ℝ => π (h.expG (s • X)) v)
    (f' := fun t : ℝ => π (h.expG (t • X)) (h.derivOp π X v)) (C := ‖h.derivOp π X v‖)
    (fun t _ => (hd t).hasDerivWithinAt) (fun t _ => (hπ _ _).le)
  simpa using hm
