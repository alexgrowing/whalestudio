import Mathlib
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.TensSmooth
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.ArchBasic
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.LactLaws
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.TensSmoothAlt
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.LactSpec

noncomputable section

open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C
open scoped TensorProduct

namespace UpperTheory.ConvolutionTheory.L1

section
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E ≃ₐ[F] E} {m : ℕ}

private def compR (D : InfD σ m) (i : Fin (m + 1)) :
    mixedEmbedding.mixedSpace E →+* mixedEmbedding.mixedSpace F :=
  (InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom.comp
    ((Pi.evalRingHom (fun _ : Fin (m + 1) => InfiniteAdeleRing F) i).comp
      (D.e.toRingHom.comp (InfiniteAdeleRing.ringEquiv_mixedSpace E).symm.toRingHom))

private theorem continuous_compR (D : InfD σ m) (i : Fin (m + 1)) : Continuous (compR D i) := by
  have he : ⇑(GroundTheory.Global.homeomorphMixedSpace E).symm =
      ⇑(InfiniteAdeleRing.ringEquiv_mixedSpace E).symm := by
    funext x
    apply (InfiniteAdeleRing.ringEquiv_mixedSpace E).injective
    rw [RingEquiv.apply_symm_apply, ← GroundTheory.Global.homeomorphMixedSpace_apply,
      Homeomorph.apply_symm_apply]
  have h1 : Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace E).symm := by
    rw [← he]; exact (GroundTheory.Global.homeomorphMixedSpace E).symm.continuous
  have h2 : Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace F) := by
    have : ⇑(InfiniteAdeleRing.ringEquiv_mixedSpace F) = ⇑(GroundTheory.Global.homeomorphMixedSpace F) := by
      funext x; rw [GroundTheory.Global.homeomorphMixedSpace_apply]
    rw [this]; exact (GroundTheory.Global.homeomorphMixedSpace F).continuous
  exact h2.comp ((continuous_apply i).comp (D.cont.comp h1))

private def compM (D : InfD σ m) (n : ℕ) (i : Fin (m + 1)) : ArchMatrix E n →+* ArchMatrix F n :=
  RingHom.mapMatrix (m := Fin n) (compR D i)

private theorem continuous_compM (D : InfD σ m) (n : ℕ) (i : Fin (m + 1)) : Continuous (compM D n i) := by
  change Continuous fun M : Matrix (Fin n) (Fin n) (mixedEmbedding.mixedSpace E) => M.map (compR D i)
  exact continuous_id.matrix_map (continuous_compR D i)

private theorem coe_compA (D : InfD σ m) (n : ℕ) (i : Fin (m + 1)) (g : archGroup E n) :
    (((compA D n i g : archGroup F n) : (ArchMatrix F n)ˣ) : ArchMatrix F n) =
      compM D n i (((g : (ArchMatrix E n)ˣ) : ArchMatrix E n)) := by
  rfl

private theorem compA_expG (D : InfD σ m) (n : ℕ) (i : Fin (m + 1)) (Y : archLie E n) (Y' : archLie F n)
    (h : compM D n i (Y : ArchMatrix E n) = Y') :
    compA D n i ((isExpLieAlgebra E n).expG Y) = (isExpLieAlgebra F n).expG Y' := by
  apply Subtype.ext
  apply Units.ext
  rw [coe_compA, IsExpLieAlgebra.coe_expG, IsExpLieAlgebra.coe_expG, ← h]
  exact NormedSpace.map_exp_of_mem_ball (𝕂 := ℝ) (compM D n i) (continuous_compM D n i) _
    ((NormedSpace.expSeries_radius_eq_top ℝ (ArchMatrix E n)).symm ▸ edist_lt_top _ _)

private theorem compR_along (D : InfD σ m) {τ : E →+* ℂ} {k : Fin (m + 1)} (h : InSlot D τ k) (z : ℂ)
    (i : Fin (m + 1)) :
    compR D i (along τ z) = if i = k then along (τ.comp (algebraMap F E)) z else 0 := by
  have e : D.e ((InfiniteAdeleRing.ringEquiv_mixedSpace E).symm (along τ z)) =
      Pi.single k ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (along (τ.comp (algebraMap F E)) z)) := by
    rw [h z, RingEquiv.apply_symm_apply]
  change InfiniteAdeleRing.ringEquiv_mixedSpace F
    (D.e ((InfiniteAdeleRing.ringEquiv_mixedSpace E).symm (along τ z)) i) = _
  rw [e]
  by_cases hik : i = k
  · subst hik
    simp
  · rw [Pi.single_eq_of_ne hik, map_zero, if_neg hik]

private def xL {K : Type} [Field K] [NumberField K] (n : ℕ) (τ : K →+* ℂ) (p q : Fin n) (z : ℂ) : archLie K n :=
  ⟨(Matrix.single p q (along τ z) : Matrix (Fin n) (Fin n) (mixedEmbedding.mixedSpace K)), Submodule.mem_top⟩

private theorem compM_xL (D : InfD σ m) (n : ℕ) {τ : E →+* ℂ} {k : Fin (m + 1)} (h : InSlot D τ k)
    (p q : Fin n) (z : ℂ) (i : Fin (m + 1)) :
    compM D n i (xL n τ p q z : ArchMatrix E n) =
      if i = k then (xL n (τ.comp (algebraMap F E)) p q z : ArchMatrix F n) else 0 := by
  change (Matrix.single p q (along τ z) : Matrix (Fin n) (Fin n) (mixedEmbedding.mixedSpace E)).map (compR D i) = _
  by_cases hik : i = k
  · rw [if_pos hik]
    ext1 a b
    change _ = (Matrix.single p q (along (τ.comp (algebraMap F E)) z) : Matrix (Fin n) (Fin n) (mixedEmbedding.mixedSpace F)) a b
    simp only [Matrix.map_apply, Matrix.single_apply]
    split_ifs
    · rw [compR_along D h, if_pos hik]
    · simp
  · rw [if_neg hik]
    ext1 a b
    change _ = (0 : Matrix (Fin n) (Fin n) (mixedEmbedding.mixedSpace F)) a b
    simp only [Matrix.map_apply, Matrix.single_apply, Matrix.zero_apply]
    split_ifs
    · rw [compR_along D h, if_neg hik]
    · simp

private theorem compA_exp_self (D : InfD σ m) (n : ℕ) {τ : E →+* ℂ} {k : Fin (m + 1)} (h : InSlot D τ k)
    (p q : Fin n) (z : ℂ) (t : ℝ) :
    compA D n k ((isExpLieAlgebra E n).expG (t • xL n τ p q z)) =
      (isExpLieAlgebra F n).expG (t • xL n (τ.comp (algebraMap F E)) p q z) := by
  apply compA_expG
  change compM D n k (t • (xL n τ p q z : ArchMatrix E n)) = t • (xL n (τ.comp (algebraMap F E)) p q z : ArchMatrix F n)
  rw [map_real_smul (compM D n k) (continuous_compM D n k), compM_xL D n h, if_pos rfl]

private theorem compA_exp_ne (D : InfD σ m) (n : ℕ) {τ : E →+* ℂ} {k i : Fin (m + 1)} (h : InSlot D τ k)
    (hi : i ≠ k) (p q : Fin n) (z : ℂ) (t : ℝ) :
    compA D n i ((isExpLieAlgebra E n).expG (t • xL n τ p q z)) = 1 := by
  rw [compA_expG D n i _ 0, IsExpLieAlgebra.expG_zero]
  change compM D n i (t • (xL n τ p q z : ArchMatrix E n)) = 0
  rw [map_real_smul (compM D n i) (continuous_compM D n i), compM_xL D n h, if_neg hi, smul_zero]

private theorem lact_elem {K : Type} [Field K] [NumberField K] {n : ℕ} (β : TI K n) (hβ : SmoothT β)
    (τ : K →+* ℂ) (p q : Fin n) (z : ℂ) (x : archGroup K n) :
    HasDerivAt (fun t : ℝ => β (x * (isExpLieAlgebra K n).expG (t • xL n τ p q z))⁻¹)
      (lact ((1 : ℂ) ⊗ₜ elem τ p q z) β x⁻¹) 0 := by
  obtain ⟨h, -, -, -, -, -, -, e⟩ := UpperTheory.ConvolutionTheory.Tf.lactSpec K n β hβ
  rw [e, inv_inv, elem, IsExpLieAlgebra.rightUAction_ι]
  exact (isExpLieAlgebra K n).hasDerivAt_rightDeriv
    (f := fun g => β g⁻¹) h (xL n τ p q z) x

private theorem leftAction_tensor_generator (D : InfD σ m) [IsTotallyComplex F] (n : ℕ) (τ : E →+* ℂ) (k : Fin (m + 1)) (hk : InSlot D τ k)
    (φ : Fin (m + 1) → TI F n) (β : TI E n) (hφ : ∀ i, SmoothT (φ i)) (hβ : IsTens D φ β) (p q : Fin n) (z : ℂ) :
    IsTens D (Function.update φ k (lact ((1 : ℂ) ⊗ₜ elem (τ.comp (algebraMap F E)) p q z) (φ k)))
      (lact ((1 : ℂ) ⊗ₜ elem τ p q z) β) := by
  have hsm : SmoothT β := (UpperTheory.ConvolutionTheory.L1.tensSmooth F E σ m D n φ β hβ).1 hφ
  intro g
  set x := g⁻¹ with hx
  have hg : g = x⁻¹ := by rw [hx, inv_inv]
  set τ' := τ.comp (algebraMap F E)
  set C : ℂ := ∏ i ∈ Finset.univ.erase k, φ i (compA D n i g) with hC
  have h1 := lact_elem β hsm τ p q z x
  have h2 := lact_elem (φ k) (hφ k) τ' p q z (compA D n k x)
  have e : (fun t : ℝ => β (x * (isExpLieAlgebra E n).expG (t • xL n τ p q z))⁻¹) =
      fun t : ℝ => φ k (compA D n k x * (isExpLieAlgebra F n).expG (t • xL n τ' p q z))⁻¹ * C := by
    funext t
    rw [hβ, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ k), map_inv (compA D n k), map_mul (compA D n k),
      compA_exp_self D n hk]
    congr 1
    refine Finset.prod_congr rfl fun i hi => ?_
    rw [map_inv (compA D n i), map_mul (compA D n i), compA_exp_ne D n hk (Finset.ne_of_mem_erase hi), mul_one, hx,
      map_inv (compA D n i), inv_inv]
  rw [e] at h1
  have h3 := h1.unique (h2.mul_const C)
  have hxk : (compA D n k x)⁻¹ = compA D n k g := by rw [hx, map_inv (compA D n k), inv_inv]
  rw [hxk, ← hg] at h3
  rw [h3, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ k), Function.update_self]
  congr 1
  rw [hC]
  exact Finset.prod_congr rfl fun i hi => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]

end

end UpperTheory.ConvolutionTheory.L1

theorem UpperTheory.ConvolutionTheory.L1.lactGen :
    UpperTheory.ConvolutionTheory.L1.LactGen := by
  intro F E _ _ _ _ _ _ σ m D n τ k hk φ β hφ hβ p q z
  exact UpperTheory.ConvolutionTheory.L1.leftAction_tensor_generator D n τ k hk φ β hφ hβ p q z
