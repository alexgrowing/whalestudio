import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.FormInverseCounting.MemHeadColsIff

noncomputable section

open Formalism.L2.SG.LocalCountModules.LocCntCommon

namespace Formalism.L2.SG.LocalCountModules.LocCnt0LAlg

variable {E : Type} [CommRing E] (O : Subring E) (cj : E →+* E) {r : ℕ}

def lamL (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) O) : (Fin (r + 1) → O) →ₗ[O] E where
  toFun y := lamC (Z.map O.subtype) (fun j => (y j : E))
  map_add' a b := by simp [lamC, Matrix.mulVec, dotProduct, mul_add, Finset.sum_add_distrib]
  map_smul' c a := by
    simp [lamC, Matrix.mulVec, dotProduct, Finset.mul_sum, Subring.smul_def, mul_left_comm]

theorem lamL_apply (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) O) (y : Fin (r + 1) → O) :
    lamL O Z y = lamC (Z.map O.subtype) (fun j => (y j : E)) := rfl

theorem lamL_mulVec (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) O) (hu : IsUnit (Z.map O.subtype).det)
    (w : Fin (r + 1) → O) : lamL O Z (Z.mulVec w) = (w (Fin.last r) : E) := by
  rw [lamL_apply, lamC]
  have hv : (fun j => ((Z.mulVec w j : O) : E)) = (Z.map O.subtype).mulVec (fun j => (w j : E)) := by
    funext j
    exact RingHom.map_mulVec O.subtype Z w j
  rw [hv, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu, Matrix.one_mulVec]

theorem lamL_K (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) O) (hu : IsUnit (Z.map O.subtype).det)
    (k : Fin (r + 1) → O) (hk : k ∈ headCols Z) : lamL O Z k = 0 := by
  obtain ⟨w, hw, rfl⟩ := (mem_headCols_iff Z k).1 hk
  rw [lamL_mulVec O Z hu, hw]; rfl

theorem bvec_eq (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) O) :
    (fun i => Z i (Fin.last r)) = Z.mulVec (Pi.single (Fin.last r) 1) := col_eq_mulVec Z _

theorem lamL_b (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) O) (hu : IsUnit (Z.map O.subtype).det) :
    lamL O Z (fun i => Z i (Fin.last r)) = 1 := by
  rw [bvec_eq, lamL_mulVec O Z hu]; simp

theorem det_smul_mk' (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) O) (v : Fin (r + 1) → O) :
    Z.det • (Submodule.Quotient.mk v : MbMod Z) =
      (Z.adjugate.mulVec v) (Fin.last r) • bCls Z := by
  rw [← Submodule.Quotient.mk_smul, bCls, ← Submodule.Quotient.mk_smul, Submodule.Quotient.eq]
  set u := Z.adjugate.mulVec v
  have hdv : Z.det • v = Z.mulVec u := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_adjugate, Matrix.smul_mulVec, Matrix.one_mulVec]
  rw [hdv, bvec_eq, ← Matrix.mulVec_smul, ← Matrix.mulVec_sub]
  exact (mem_headCols_iff Z _).mpr ⟨_, by simp, rfl⟩

theorem det_coe (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) O) : ((Z.det : O) : E) = (Z.map O.subtype).det := by
  exact RingHom.map_det O.subtype Z

theorem det_mul_lamL (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) O) (hu : IsUnit (Z.map O.subtype).det)
    (v : Fin (r + 1) → O) :
    (Z.det : E) * lamL O Z v = ((Z.adjugate.mulVec v) (Fin.last r) : E) := by
  rw [det_coe, lamL_apply, lamC, Matrix.inv_def, Matrix.smul_mulVec, Pi.smul_apply, smul_eq_mul,
    ← mul_assoc, Ring.mul_inverse_cancel _ hu, one_mul]
  have h1 := RingHom.map_mulVec O.subtype Z.adjugate v (Fin.last r)
  have h2 := RingHom.map_adjugate O.subtype Z
  simp only [RingHom.mapMatrix_apply] at h2
  rw [← h2] at *
  exact h1.symm

theorem lam_keep {Z₁ Z₂ : Matrix (Fin (r + 1)) (Fin (r + 1)) O} (hu₁ : IsUnit (Z₁.map O.subtype).det)
    (hu₂ : IsUnit (Z₂.map O.subtype).det) (γ : MbMod Z₁ →ₗ[O] MbMod Z₂) (hb : γ (bCls Z₁) = bCls Z₂)
    (y₁ y₂ : Fin (r + 1) → O)
    (h : γ (Submodule.Quotient.mk y₁) = Submodule.Quotient.mk y₂) : lamL O Z₂ y₂ = lamL O Z₁ y₁ := by
  let Λ := (headCols Z₂).liftQ (lamL O Z₂) (fun k hk => LinearMap.mem_ker.mpr (lamL_K O Z₂ hu₂ k hk))
  have hΛb : Λ (bCls Z₂) = 1 := lamL_b O Z₂ hu₂
  have hΛy : Λ (Submodule.Quotient.mk y₂) = lamL O Z₂ y₂ := rfl
  have key := congrArg (fun q => Λ (γ q)) (det_smul_mk' O Z₁ y₁)
  simp only [map_smul, hb, h, hΛb, hΛy] at key
  have hdet : IsUnit ((Z₁.det : O) : E) := by rw [det_coe]; exact hu₁
  apply hdet.mul_left_cancel
  rw [det_mul_lamL O Z₁ hu₁ y₁]
  rw [Subring.smul_def, Subring.smul_def, smul_eq_mul, smul_eq_mul, mul_one] at key
  exact key

end Formalism.L2.SG.LocalCountModules.LocCnt0LAlg
