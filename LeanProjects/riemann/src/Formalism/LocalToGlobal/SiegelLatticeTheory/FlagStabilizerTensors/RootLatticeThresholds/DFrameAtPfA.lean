import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.StepPtRepPfD

noncomputable section

open Matrix Formalism.MainNotions.S

namespace Formalism.L2.SG.Pf.Carrier.DFrameAtPf

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.L2.SG.RealObj.InfCut.PtRepPf

theorem exists_unitary_of_gram {k : ℕ} {M : Type*} [AddCommGroup M] [Module ℂ M]
    (α β : M →ₗ[ℂ] (Fin k → ℂ)) (h : ∀ p q, star (α p) ⬝ᵥ α q = star (β p) ⬝ᵥ β q) :
    ∃ ψ ∈ Matrix.unitaryGroup (Fin k) ℂ, ∀ p, ψ *ᵥ α p = β p := by
  let T : (Fin k → ℂ) ≃ₗ[ℂ] EuclideanSpace ℂ (Fin k) := (WithLp.linearEquiv 2 ℂ (Fin k → ℂ)).symm
  have hT : ∀ u v, inner ℂ (T u) (T v) = star u ⬝ᵥ v := by
    intro u v
    rw [dotProduct_comm]
    rfl
  let a : M →ₗ[ℂ] EuclideanSpace ℂ (Fin k) := T.toLinearMap ∘ₗ α
  let b : M →ₗ[ℂ] EuclideanSpace ℂ (Fin k) := T.toLinearMap ∘ₗ β
  have hab : ∀ p q, inner ℂ (a p) (a q) = inner ℂ (b p) (b q) := by
    intro p q
    simp only [a, b, LinearMap.comp_apply, LinearEquiv.coe_coe, hT, h]
  have hker : LinearMap.ker a ≤ LinearMap.ker b := by
    intro p hp
    rw [LinearMap.mem_ker] at hp ⊢
    have h2 := hab p p
    rw [hp, inner_zero_left, eq_comm, inner_self_eq_zero] at h2
    exact h2
  let g : LinearMap.range a →ₗ[ℂ] EuclideanSpace ℂ (Fin k) :=
    (LinearMap.ker a).liftQ b hker ∘ₗ (LinearMap.quotKerEquivRange a).symm.toLinearMap
  have hg : ∀ p, g ⟨a p, LinearMap.mem_range_self a p⟩ = b p := by
    intro p
    simp only [g, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearMap.quotKerEquivRange_symm_apply_image, Submodule.mkQ_apply, Submodule.liftQ_apply]
  have hgi : ∀ s t : LinearMap.range a, inner ℂ (g s) (g t) = inner ℂ s t := by
    rintro ⟨_, p, rfl⟩ ⟨_, q, rfl⟩
    rw [hg, hg, Submodule.coe_inner]
    exact (hab p q).symm
  let F := (g.isometryOfInner hgi).extend
  have hF : ∀ p, F (a p) = b p := by
    intro p
    have := LinearIsometry.extend_apply (g.isometryOfInner hgi) ⟨a p, LinearMap.mem_range_self a p⟩
    rw [LinearMap.coe_isometryOfInner, hg] at this
    exact this
  let ψ : Matrix (Fin k) (Fin k) ℂ :=
    LinearMap.toMatrix' (T.symm.toLinearMap ∘ₗ F.toLinearMap ∘ₗ T.toLinearMap)
  have hψ : ∀ u, ψ *ᵥ u = T.symm (F (T u)) := by
    intro u
    simp only [ψ, LinearMap.toMatrix'_mulVec, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearIsometry.coe_toLinearMap]
  have hiso : ∀ u v, star (ψ *ᵥ u) ⬝ᵥ (ψ *ᵥ v) = star u ⬝ᵥ v := by
    intro u v
    rw [← hT, ← hT, hψ, hψ, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply,
      LinearIsometry.inner_map_map]
  refine ⟨ψ, ?_, fun p => ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff']
    ext i j
    have := hiso (Pi.single i 1) (Pi.single j 1)
    simp [Matrix.mul_apply, dotProduct, Matrix.one_apply] at this ⊢
    rw [this]
    by_cases hij : i = j
    · subst hij
      simp [Pi.single_apply]
    · simp [Pi.single_apply, hij]
      exact Ne.symm hij
  · rw [hψ]
    have := hF p
    simp only [a, b, LinearMap.comp_apply, LinearEquiv.coe_coe] at this
    rw [this, LinearEquiv.symm_apply_apply]

section Lift

variable {n k : ℕ} (ε : Fin n → Bool)

def liftV (wb : Fin k → Fin n → ℂ) (U : Matrix (Fin k) (Fin k) ℂ) (y : Fin n → ℂ) : Fin n → ℂ :=
  y + ∑ a, ((U - 1) *ᵥ wCoord ε wb y) a • wb a

def liftL (wb : Fin k → Fin n → ℂ) (U : Matrix (Fin k) (Fin k) ℂ) : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ) where
  toFun := liftV ε wb U
  map_add' x y := by
    have hw : wCoord ε wb (x + y) = wCoord ε wb x + wCoord ε wb y := by
      funext i; simp [wCoord, hJ_add_right]
    simp only [liftV, hw, mulVec_add, Pi.add_apply, add_smul, Finset.sum_add_distrib]
    abel
  map_smul' c x := by
    have hw : wCoord ε wb (c • x) = c • wCoord ε wb x := by
      funext i; simp [wCoord, hJ_smul_right]
    simp only [liftV, hw, mulVec_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, smul_add,
      Finset.smul_sum, smul_smul]

def liftM (wb : Fin k → Fin n → ℂ) (U : Matrix (Fin k) (Fin k) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  LinearMap.toMatrix' (liftL ε wb U)

theorem liftM_mulVec (wb : Fin k → Fin n → ℂ) (U : Matrix (Fin k) (Fin k) ℂ) (y : Fin n → ℂ) :
    liftM ε wb U *ᵥ y = y + ∑ a, ((U - 1) *ᵥ wCoord ε wb y) a • wb a := by
  rw [liftM, LinearMap.toMatrix'_mulVec]; rfl

variable {ε}

theorem hJ_wb_sum {wb : Fin k → Fin n → ℂ} (hon : ∀ i j, hJ ε (wb i) (wb j) = if i = j then 1 else 0)
    (c : Fin k) (p : Fin k → ℂ) : hJ ε (wb c) (∑ a, p a • wb a) = p c := by
  rw [hJ_sum_right]
  simp only [hJ_smul_right, hon, mul_ite, mul_one, mul_zero]
  simp

theorem wCoord_liftM {wb : Fin k → Fin n → ℂ} (hon : ∀ i j, hJ ε (wb i) (wb j) = if i = j then 1 else 0)
    (U : Matrix (Fin k) (Fin k) ℂ) (y : Fin n → ℂ) :
    wCoord ε wb (liftM ε wb U *ᵥ y) = U *ᵥ wCoord ε wb y := by
  funext c
  show hJ ε (wb c) (liftM ε wb U *ᵥ y) = (U *ᵥ wCoord ε wb y) c
  rw [liftM_mulVec, hJ_add_right, hJ_wb_sum hon, sub_mulVec, one_mulVec, Pi.sub_apply]
  show wCoord ε wb y c + _ = _
  ring

theorem liftM_fix {wb : Fin k → Fin n → ℂ} (U : Matrix (Fin k) (Fin k) ℂ) (y : Fin n → ℂ)
    (hy : ∀ i, hJ ε (wb i) y = 0) : liftM ε wb U *ᵥ y = y := by
  have h0 : wCoord ε wb y = 0 := funext hy
  rw [liftM_mulVec, h0, mulVec_zero]
  simp

private theorem liftM_iso_lemma {wb : Fin k → Fin n → ℂ} (p : Fin k → ℂ) (y : Fin n → ℂ) :
    hJ ε (∑ a, p a • wb a) y = star p ⬝ᵥ wCoord ε wb y := by
  rw [hJ_sum_left]
  simp only [hJ_smul_left, dotProduct, wCoord, Pi.star_apply]

private theorem liftM_iso_lemma_2 {wb : Fin k → Fin n → ℂ} (p : Fin k → ℂ) (x : Fin n → ℂ) :
    hJ ε x (∑ a, p a • wb a) = star (wCoord ε wb x) ⬝ᵥ p := by
  rw [hJ_sum_right]
  simp only [hJ_smul_right, dotProduct, wCoord, Pi.star_apply, hJ_conj]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

private theorem liftM_iso_lemma_3 {wb : Fin k → Fin n → ℂ}
    (hon : ∀ i j, hJ ε (wb i) (wb j) = if i = j then 1 else 0) (q p : Fin k → ℂ) :
    hJ ε (∑ a, q a • wb a) (∑ a, p a • wb a) = star q ⬝ᵥ p := by
  rw [liftM_iso_lemma]
  congr 1
  funext c
  exact hJ_wb_sum hon c p

theorem liftM_iso {wb : Fin k → Fin n → ℂ} (hon : ∀ i j, hJ ε (wb i) (wb j) = if i = j then 1 else 0)
    (U : Matrix (Fin k) (Fin k) ℂ) (hU : U ∈ Matrix.unitaryGroup (Fin k) ℂ) (x y : Fin n → ℂ) :
    hJ ε (liftM ε wb U *ᵥ x) (liftM ε wb U *ᵥ y) = hJ ε x y := by
  have hu : Uᴴ * U = 1 := by
    have h := Matrix.mem_unitaryGroup_iff'.mp hU
    rwa [Matrix.star_eq_conjTranspose] at h
  have key : (U - 1) + (U - 1)ᴴ + (U - 1)ᴴ * (U - 1) = 0 := by
    simp only [conjTranspose_sub, conjTranspose_one, sub_mul, mul_sub, mul_one, one_mul, hu]
    abel
  rw [liftM_mulVec, liftM_mulVec, hJ_add_left, hJ_add_right, hJ_add_right, liftM_iso_lemma_3 hon,
    liftM_iso_lemma_2, liftM_iso_lemma]
  have e : ∀ a b : Fin k → ℂ, star a ⬝ᵥ ((U - 1) *ᵥ b) + (star ((U - 1) *ᵥ a) ⬝ᵥ b
      + star ((U - 1) *ᵥ a) ⬝ᵥ ((U - 1) *ᵥ b))
      = star a ⬝ᵥ (((U - 1) + (U - 1)ᴴ + (U - 1)ᴴ * (U - 1)) *ᵥ b) := by
    intro a b
    rw [star_mulVec, ← dotProduct_mulVec, ← dotProduct_mulVec, add_mulVec, add_mulVec,
      ← mulVec_mulVec, dotProduct_add, dotProduct_add]
    ring
  rw [add_assoc, e, key, zero_mulVec, dotProduct_zero, add_zero]

def liftU (wb : Fin k → Fin n → ℂ) (hon : ∀ i j, hJ ε (wb i) (wb j) = if i = j then 1 else 0)
    (U : Matrix (Fin k) (Fin k) ℂ) (hU : U ∈ Matrix.unitaryGroup (Fin k) ℂ) : Formalism.REAL.UJ ε :=
  ⟨(Matrix.isUnit_iff_isUnit_det _).2 (by
      have hA := inUJ_of_iso ε _ (liftM_iso hon U hU)
      unfold Formalism.REAL.inUJ at hA
      have h1 := congrArg Matrix.det hA
      rw [det_mul, det_mul] at h1
      have hJ0 : (Formalism.REAL.Jm ε).det ≠ 0 := by
        unfold Formalism.REAL.Jm
        rw [det_diagonal]
        exact Finset.prod_ne_zero_iff.2 fun a _ => by split_ifs <;> norm_num
      refine isUnit_iff_ne_zero.2 fun h0 => hJ0 ?_
      rw [← h1, show (liftM ε wb U).det = 0 from h0, mul_zero])|>.unit, inUJ_of_iso ε _ (liftM_iso hon U hU)⟩

theorem liftU_mulVec (wb : Fin k → Fin n → ℂ) (hon : ∀ i j, hJ ε (wb i) (wb j) = if i = j then 1 else 0)
    (U : Matrix (Fin k) (Fin k) ℂ) (hU : U ∈ Matrix.unitaryGroup (Fin k) ℂ) (y : Fin n → ℂ) :
    uMat (liftU wb hon U hU) *ᵥ y = liftM ε wb U *ᵥ y := rfl

end Lift

end Formalism.L2.SG.Pf.Carrier.DFrameAtPf
