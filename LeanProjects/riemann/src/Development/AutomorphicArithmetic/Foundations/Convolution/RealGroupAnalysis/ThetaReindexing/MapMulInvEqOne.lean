import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.Smooth
import GroundTheory.HeightsAndTheta.Theta.AdelicFourierCoord

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2
open scoped Classical

namespace UpperTheory.ConvolutionTheory.R2.D

open GroundTheory.Heights₂.Theta NumberField.mixedEmbedding

section

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι] [DecidableEq ι]

private theorem map_mul_inv_eq_one {R : Type} [CommRing R] (h : A K →+* R) (g : GL ι (A K)) :
    g.val.map h * (g⁻¹).val.map h = 1 := by
  rw [← Matrix.map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
    Matrix.map_one h (map_zero h) (map_one h)]

private theorem map_inv_mul_eq_one {R : Type} [CommRing R] (h : A K →+* R) (g : GL ι (A K)) :
    (g⁻¹).val.map h * g.val.map h = 1 := by
  rw [← Matrix.map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
    Matrix.map_one h (map_zero h) (map_one h)]

private noncomputable def infEquiv (g : GL ι (A K)) :
    (ι → mixedSpace K) ≃L[ℝ] (ι → mixedSpace K) :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := fun u ↦ g.val.map adeleInfHom *ᵥ u
      invFun := fun u ↦ (g⁻¹).val.map adeleInfHom *ᵥ u
      map_add' := fun u v ↦ Matrix.mulVec_add _ u v
      map_smul' := fun c u ↦ Matrix.mulVec_smul _ c u
      left_inv := fun u ↦ by
        simp only [Matrix.mulVec_mulVec, map_inv_mul_eq_one, Matrix.one_mulVec]
      right_inv := fun u ↦ by
        simp only [Matrix.mulVec_mulVec, map_mul_inv_eq_one, Matrix.one_mulVec] }

private noncomputable def finHomeo (g : GL ι (A K)) :
    (ι → FiniteAdeleRing (𝓞 K) K) ≃ₜ (ι → FiniteAdeleRing (𝓞 K) K) where
  toFun u := g.val.map adeleFinHom *ᵥ u
  invFun u := (g⁻¹).val.map adeleFinHom *ᵥ u
  left_inv u := by
    simp only [Matrix.mulVec_mulVec, map_inv_mul_eq_one, Matrix.one_mulVec]
  right_inv u := by
    simp only [Matrix.mulVec_mulVec, map_mul_inv_eq_one, Matrix.one_mulVec]
  continuous_toFun := continuous_const.matrix_mulVec continuous_id
  continuous_invFun := continuous_const.matrix_mulVec continuous_id

private theorem infPartPi_gl (g : GL ι (A K)) (x : ι → A K) :
    infPartPi (g.val *ᵥ x) = infEquiv g (infPartPi x) := by
  rw [infPartPi_eq_adeleInfHom, infPartPi_eq_adeleInfHom, map_mulVec_eq]
  rfl

private theorem finPartPi_gl (g : GL ι (A K)) (x : ι → A K) :
    finPartPi (g.val *ᵥ x) = finHomeo g (finPartPi x) := by
  rw [finPartPi_eq_adeleFinHom, finPartPi_eq_adeleFinHom, map_mulVec_eq]
  rfl

end

end UpperTheory.ConvolutionTheory.R2.D

theorem UpperTheory.ConvolutionTheory.R2.D.sClos :
    ∀ (F : Type) [Field F] [NumberField F] (ι : Type) [Fintype ι] [DecidableEq ι] (g : GL ι (A F)) (φ : (ι → A F) → ℂ),
    φ ∈ schwartzBruhatPi F ι → (fun v => φ (g.val *ᵥ v)) ∈ schwartzBruhatPi F ι := by
  intro F _ _ ι _ _ g φ hφ
  induction hφ using Submodule.span_induction with
  | mem G hG =>
    obtain ⟨f, h, hh, rfl⟩ := hG
    have e : (fun v => schwartzBruhatTensorPi f h (g.val *ᵥ v)) =
        schwartzBruhatTensorPi (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (infEquiv g) f)
          (h ∘ finHomeo g) := by
      funext x
      simp only [schwartzBruhatTensorPi, SchwartzMap.compCLMOfContinuousLinearEquiv_apply,
        Function.comp_apply, infPartPi_gl, finPartPi_gl]
    rw [e]
    refine schwartzBruhatTensorPi_mem _ ((mem_finiteSchwartzBruhatPi F).2 ⟨?_, ?_⟩)
    · exact ((mem_finiteSchwartzBruhatPi F).1 hh).1.comp_continuous (finHomeo g).continuous
    · exact ((mem_finiteSchwartzBruhatPi F).1 hh).2.comp_homeomorph (finHomeo g)
  | zero => exact zero_mem _
  | add G H _ _ hG hH => exact add_mem hG hH
  | smul c G _ hG => exact Submodule.smul_mem _ c hG
