import Formalism.HermitianCurvature.HermitianCurvatureProofs.BetaSesquilinearity

open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.HilbertSchmidtVectorization

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

def hsInv (v : PiLp 2 (fun _ : Fin (Module.finrank ℂ Wq) => Wp)) : Wq →L[ℂ] Wp :=
  LinearMap.toContinuousLinearMap ((stdOrthonormalBasis ℂ Wq).toBasis.constr ℂ (fun i => v i))

lemma hsInv_basis (v : PiLp 2 (fun _ : Fin (Module.finrank ℂ Wq) => Wp)) (i : Fin (Module.finrank ℂ Wq)) :
    hsInv v (stdOrthonormalBasis ℂ Wq i) = v i := by
  have := (stdOrthonormalBasis ℂ Wq).toBasis.constr_basis ℂ (fun i => v i) i
  simpa [hsInv] using this

lemma hsVec_apply' (A : Wq →L[ℂ] Wp) (i : Fin (Module.finrank ℂ Wq)) :
    hsVec A i = A (stdOrthonormalBasis ℂ Wq i) := rfl

lemma hsInv_hsVec (A : Wq →L[ℂ] Wp) : hsInv (hsVec A) = A := by
  apply ContinuousLinearMap.coe_injective
  apply (stdOrthonormalBasis ℂ Wq).toBasis.ext
  intro i
  simp only [ContinuousLinearMap.coe_coe, OrthonormalBasis.coe_toBasis]
  rw [hsInv_basis, hsVec_apply']

lemma hsVec_hsInv (v : PiLp 2 (fun _ : Fin (Module.finrank ℂ Wq) => Wp)) : hsVec (hsInv v) = v := by
  ext i
  rw [hsVec_apply', hsInv_basis]

def hsE : (Wq →L[ℂ] Wp) ≃ₗ[ℂ] PiLp 2 (fun _ : Fin (Module.finrank ℂ Wq) => Wp) where
  toFun := hsVec
  map_add' A B := by ext i; simp [hsVec_apply']
  map_smul' c A := by ext i; simp [hsVec_apply']
  invFun := hsInv
  left_inv := hsInv_hsVec
  right_inv := hsVec_hsInv

def conjE (T : (Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp)) :
    PiLp 2 (fun _ : Fin (Module.finrank ℂ Wq) => Wp) →L[ℂ] PiLp 2 (fun _ : Fin (Module.finrank ℂ Wq) => Wp) :=
  LinearMap.toContinuousLinearMap (hsE.toLinearMap ∘ₗ T.toLinearMap ∘ₗ hsE.symm.toLinearMap)

def adjH (T : (Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp)) : (Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp) :=
  LinearMap.toContinuousLinearMap
    (hsE.symm.toLinearMap ∘ₗ (ContinuousLinearMap.adjoint (conjE T)).toLinearMap ∘ₗ hsE.toLinearMap)

lemma hsE_adjH (T : (Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp)) (B : Wq →L[ℂ] Wp) :
    hsVec (adjH T B) = ContinuousLinearMap.adjoint (conjE T) (hsVec B) := by
  show hsE (hsE.symm _) = _
  rw [LinearEquiv.apply_symm_apply]; rfl

lemma conjE_hsVec (T : (Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp)) (A : Wq →L[ℂ] Wp) :
    conjE T (hsVec A) = hsVec (T A) := by
  show hsE (T (hsE.symm (hsE A))) = _
  rw [LinearEquiv.symm_apply_apply]; rfl

theorem adjH_spec (T : (Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp)) (A B : Wq →L[ℂ] Wp) :
    hsInner (T A) B = hsInner A (adjH T B) := by
  unfold hsInner
  rw [hsE_adjH, ContinuousLinearMap.adjoint_inner_left, conjE_hsVec]

lemma adjH_add (T S : (Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp)) : adjH (T + S) = adjH T + adjH S := by
  ext B : 1
  apply hsE.injective
  simp only [ContinuousLinearMap.add_apply, map_add]
  show hsVec (adjH (T + S) B) = hsVec (adjH T B) + hsVec (adjH S B)
  rw [hsE_adjH, hsE_adjH, hsE_adjH]
  have : conjE (T + S) = conjE T + conjE S := by
    ext v : 1; simp [conjE]
  rw [this, map_add, ContinuousLinearMap.add_apply]

lemma adjH_smulC (c : ℂ) (T : (Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp)) : adjH (c • T) = (starRingEnd ℂ c) • adjH T := by
  ext B : 1
  apply hsE.injective
  show hsVec (adjH (c • T) B) = hsE (((starRingEnd ℂ c) • adjH T) B)
  rw [ContinuousLinearMap.smul_apply, map_smul]
  show _ = (starRingEnd ℂ c) • hsVec (adjH T B)
  rw [hsE_adjH, hsE_adjH]
  have : conjE (c • T) = c • conjE T := by
    ext v : 1; simp [conjE]
  rw [this, map_smulₛₗ, ContinuousLinearMap.smul_apply]

lemma adjH_smul (c : ℝ) (T : (Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp)) : adjH (c • T) = c • adjH T := by
  rw [← Complex.coe_smul, adjH_smulC, Complex.conj_ofReal, Complex.coe_smul]

def adjR : ((Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp)) →L[ℝ] ((Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp)) :=
  LinearMap.toContinuousLinearMap
    { toFun := adjH
      map_add' := adjH_add
      map_smul' := adjH_smul }

lemma adjR_apply (T : (Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp)) : adjR T = adjH T := rfl

end Formalism.FourierDecayAlt.P.HilbertSchmidtVectorization
