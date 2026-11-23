import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsTangentGaussInvariant
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PConeIntegralMass
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory Module

open scoped Matrix

open scoped ENNReal

noncomputable section

def unitMat {n : ℕ} (U : EuclideanSpace ℂ (Fin n) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin n)) :
    Matrix (Fin n) (Fin n) ℂ :=
  LinearMap.toMatrix (EuclideanSpace.basisFun (Fin n) ℂ).toBasis
    (EuclideanSpace.basisFun (Fin n) ℂ).toBasis U.toLinearMap

theorem unitMat_mem {n : ℕ} (U : EuclideanSpace ℂ (Fin n) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin n)) :
    unitMat U ∈ Matrix.unitaryGroup (Fin n) ℂ :=
  U.toMatrix_mem_unitaryGroup _ _

theorem unitary_apply_eq_sum {n : ℕ} (U : EuclideanSpace ℂ (Fin n) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin n))
    (v : EuclideanSpace ℂ (Fin n)) (k : Fin n) : U v k = ∑ j, unitMat U k j * v j := by
  have h := LinearMap.toMatrix_mulVec_repr (EuclideanSpace.basisFun (Fin n) ℂ).toBasis
    (EuclideanSpace.basisFun (Fin n) ℂ).toBasis U.toLinearMap v
  have h2 := congrFun h k
  simpa [unitMat, Matrix.mulVec, dotProduct] using h2.symm

theorem unitMat_mul_symm {n : ℕ} (U : EuclideanSpace ℂ (Fin n) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin n)) :
    unitMat U * unitMat U.symm = 1 := by
  rw [unitMat, unitMat, ← LinearMap.toMatrix_mul]
  have : U.toLinearMap * U.symm.toLinearMap = 1 := LinearMap.ext fun x => by simp
  rw [this, LinearMap.toMatrix_one]

theorem sum_norm_sq_vecMul {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : A ∈ Matrix.unitaryGroup (Fin n) ℂ) (r : Fin n → ℂ) :
    ∑ j, ‖(r ᵥ* A) j‖ ^ 2 = ∑ j, ‖r j‖ ^ 2 := by
  have key : ∀ s : Fin n → ℂ, ((∑ j, ‖s j‖ ^ 2 : ℝ) : ℂ) = s ⬝ᵥ star s := by
    intro s
    simp [dotProduct, Complex.mul_conj']
  apply Complex.ofReal_injective
  rw [key (r ᵥ* A), key r, Matrix.star_vecMul, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul,
    ← Matrix.star_eq_conjTranspose, (Matrix.mem_unitaryGroup_iff).1 hA, Matrix.vecMul_one]

theorem measurePreserving_vecMul {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : A ∈ Matrix.unitaryGroup (Fin n) ℂ) :
    MeasurePreserving (fun r : Fin n → ℂ => r ᵥ* A) volume volume := by
  set f : (Fin n → ℂ) →ₗ[ℝ] (Fin n → ℂ) := (Matrix.toLin' Aᵀ).restrictScalars ℝ with hf
  have hfun : (fun r : Fin n → ℂ => r ᵥ* A) = f := by
    funext r
    simp [hf, Matrix.toLin'_apply, Matrix.mulVec_transpose]
  have hdet : LinearMap.det f = 1 := by
    have hd : ‖A.det‖ = 1 := by
      have h1 : A.det ∈ unitary ℂ := Matrix.det_of_mem_unitary hA
      exact CStarRing.norm_of_mem_unitary h1
    rw [hf, LinearMap.det_restrictScalars, LinearMap.det_toLin', Matrix.det_transpose,
      Algebra.norm_complex_apply, Complex.normSq_eq_norm_sq, hd]
    norm_num
  have hmeas : Measurable (fun r : Fin n → ℂ => r ᵥ* A) := by
    apply Continuous.measurable
    fun_prop
  refine ⟨hmeas, ?_⟩
  rw [hfun, Measure.map_linearMap_addHaar_eq_smul_addHaar volume (by rw [hdet]; norm_num), hdet]
  simp

def matSub {m n : ℕ} (U : EuclideanSpace ℂ (Fin n) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin n))
    (π : Fin m → Fin n → ℂ) : Fin m → Fin n → ℂ :=
  fun i => π i ᵥ* unitMat U

theorem measurePreserving_matSub {m n : ℕ}
    (U : EuclideanSpace ℂ (Fin n) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin n)) :
    MeasurePreserving (matSub (m := m) U) volume volume :=
  volume_preserving_pi fun _ => measurePreserving_vecMul (unitMat_mem U)

theorem matSub_symm_matSub {m n : ℕ}
    (U : EuclideanSpace ℂ (Fin n) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin n)) (π : Fin m → Fin n → ℂ) :
    matSub U.symm (matSub U π) = π := by
  funext i
  simp [matSub, Matrix.vecMul_vecMul, unitMat_mul_symm]

def matSubEquiv {m n : ℕ} (U : EuclideanSpace ℂ (Fin n) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin n)) :
    (Fin m → Fin n → ℂ) ≃ᵐ (Fin m → Fin n → ℂ) where
  toFun := matSub U
  invFun := matSub U.symm
  left_inv := matSub_symm_matSub U
  right_inv π := by simpa using matSub_symm_matSub U.symm π
  measurable_toFun := (measurePreserving_matSub U).measurable
  measurable_invFun := (measurePreserving_matSub U.symm).measurable

theorem linProj_matSub {m n : ℕ} (U : EuclideanSpace ℂ (Fin n) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin n))
    (π : Fin m → Fin n → ℂ) (v : EuclideanSpace ℂ (Fin n)) :
    linProj (matSub U π) v = linProj π (U v) := by
  simp only [linProj, matSub, unitary_apply_eq_sum, Matrix.vecMul, dotProduct]
  congr 1
  funext i
  simp_rw [Finset.sum_mul, Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

theorem matGauss_matSub {m n : ℕ} (U : EuclideanSpace ℂ (Fin n) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin n))
    (π : Fin m → Fin n → ℂ) : matGauss (matSub U π) = matGauss π := by
  simp only [matGauss, matSub, sum_norm_sq_vecMul (unitMat_mem U)]

theorem firstCoordVec_eq_basisFun {n : ℕ} (hn : 0 < n) :
    firstCoordVec n = EuclideanSpace.basisFun (Fin n) ℂ ⟨0, hn⟩ := by
  ext j
  simp [firstCoordVec, EuclideanSpace.basisFun_apply, Fin.ext_iff]

theorem exists_unitary_leadCoordPlane {n m : ℕ} (hm : 0 < m) (hmn : m ≤ n)
    (T : Submodule ℂ (EuclideanSpace ℂ (Fin n))) (hT : finrank ℂ T = m)
    (y : EuclideanSpace ℂ (Fin n)) (hy : y ∈ T) :
    ∃ U : EuclideanSpace ℂ (Fin n) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin n),
      (∀ v ∈ leadCoordPlane n m, U v ∈ T) ∧ (∀ t ∈ T, ∃ v ∈ leadCoordPlane n m, U v = t) ∧
        U ((‖y‖ : ℂ) • firstCoordVec n) = y := by
  classical
  have hn : 0 < n := lt_of_lt_of_le hm hmn
  obtain ⟨u, huT, hu1, hyu⟩ : ∃ u ∈ T, ‖u‖ = 1 ∧ (‖y‖ : ℂ) • u = y := by
    by_cases hy0 : y = 0
    · have hTne : T ≠ ⊥ := by
        intro h
        rw [h, finrank_bot] at hT
        omega
      obtain ⟨t, htT, ht0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hTne
      exact ⟨(‖t‖⁻¹ : ℂ) • t, T.smul_mem _ htT, norm_smul_inv_norm ht0, by simp [hy0]⟩
    · refine ⟨(‖y‖⁻¹ : ℂ) • y, T.smul_mem _ hy, norm_smul_inv_norm hy0, ?_⟩
      rw [smul_smul, mul_inv_cancel₀ (by exact_mod_cast norm_ne_zero_iff.2 hy0), one_smul]
  obtain ⟨bT, hbT⟩ := Orthonormal.exists_orthonormalBasis_extension_of_card_eq (𝕜 := ℂ) (E := T)
    (ι := Fin m) (v := fun _ => (⟨u, huT⟩ : T)) (s := {⟨0, hm⟩}) (by simp [hT]) (by
      refine ⟨fun i => by simpa using hu1, fun i j hij => ?_⟩
      exact absurd (Subtype.ext ((Set.mem_singleton_iff.1 i.2).trans
        (Set.mem_singleton_iff.1 j.2).symm)) hij)
  have hbT0 : (bT ⟨0, hm⟩ : EuclideanSpace ℂ (Fin n)) = u := by
    rw [hbT _ (Set.mem_singleton _)]
  set v : Fin n → EuclideanSpace ℂ (Fin n) :=
    fun j => if h : (j : ℕ) < m then (bT ⟨j, h⟩ : EuclideanSpace ℂ (Fin n)) else 0 with hv
  obtain ⟨B, hB⟩ := Orthonormal.exists_orthonormalBasis_extension_of_card_eq (𝕜 := ℂ)
    (E := EuclideanSpace ℂ (Fin n)) (ι := Fin n) (v := v) (s := {j | (j : ℕ) < m}) (by simp) (by
      rw [orthonormal_iff_ite]
      rintro ⟨i, hi⟩ ⟨j, hj⟩
      have hi' : (i : ℕ) < m := hi
      have hj' : (j : ℕ) < m := hj
      simp only [Set.domRestrict, hv, dif_pos hi', dif_pos hj']
      rw [← Submodule.coe_inner, orthonormal_iff_ite.1 bT.orthonormal]
      simp [Fin.ext_iff])
  have hBv : ∀ j : Fin n, ∀ h : (j : ℕ) < m, B j = (bT ⟨j, h⟩ : EuclideanSpace ℂ (Fin n)) := by
    intro j h
    rw [hB j h]
    simp [hv, h]
  set e := EuclideanSpace.basisFun (Fin n) ℂ with he
  have hU : ∀ w, e.equiv B (Equiv.refl _) w = ∑ j, w j • B j := by
    intro w
    conv_lhs => rw [← e.sum_repr w]
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, OrthonormalBasis.equiv_apply_basis, Equiv.refl_apply]
    rfl
  refine ⟨e.equiv B (Equiv.refl _), ?_, ?_, ?_⟩
  · intro w hw
    have hw' : ∀ j : Fin n, m ≤ (j : ℕ) → w j = 0 := hw
    rw [hU]
    refine Submodule.sum_mem _ fun j _ => ?_
    by_cases h : (j : ℕ) < m
    · rw [hBv j h]
      exact T.smul_mem _ (bT _).2
    · rw [hw' j (by omega), zero_smul]
      exact T.zero_mem
  · intro t ht
    have hBk : ∀ k : Fin m, B (Fin.castLE hmn k) = (bT k : EuclideanSpace ℂ (Fin n)) :=
      fun k => hBv _ (by simp)
    refine ⟨∑ k : Fin m, (bT.repr ⟨t, ht⟩ k) • e (Fin.castLE hmn k), ?_, ?_⟩
    · refine Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ ?_
      show ∀ j : Fin n, m ≤ (j : ℕ) → (e (Fin.castLE hmn k)) j = 0
      intro j hj
      have hne : j ≠ Fin.castLE hmn k := by
        intro h
        have := congrArg Fin.val h
        simp at this
        omega
      simp [he, EuclideanSpace.basisFun_apply, hne]
    · calc e.equiv B (Equiv.refl _) (∑ k : Fin m, (bT.repr ⟨t, ht⟩ k) • e (Fin.castLE hmn k))
            = ∑ k : Fin m, (bT.repr ⟨t, ht⟩ k) • (bT k : EuclideanSpace ℂ (Fin n)) := by
              simp [map_sum, map_smul, OrthonormalBasis.equiv_apply_basis, hBk]
        _ = ((∑ k : Fin m, (bT.repr ⟨t, ht⟩ k) • bT k : T) : EuclideanSpace ℂ (Fin n)) := by
              simp
        _ = t := by rw [bT.sum_repr]
  · rw [firstCoordVec_eq_basisFun hn, map_smul, OrthonormalBasis.equiv_apply_basis,
      Equiv.refl_apply, hBv _ hm]
    rw [show (⟨((⟨0, hn⟩ : Fin n) : ℕ), hm⟩ : Fin m) = ⟨0, hm⟩ from rfl, hbT0, hyu]

theorem TangentGaussInvariant.proof : TangentGaussInvariant.Statement := by
  intro n m hm hmn T hT y hy
  obtain ⟨U, hLT, hTL, hUy⟩ := exists_unitary_leadCoordPlane hm hmn T hT y hy
  set L := leadCoordPlane n m with hL
  let W : L →ₗᵢ[ℂ] T :=
    { toFun := fun x => ⟨U x, hLT x x.2⟩
      map_add' := fun x x' => by ext1; simp
      map_smul' := fun c x => by ext1; simp
      norm_map' := fun x => by simp }
  have hWx : ∀ x : L, (W x : EuclideanSpace ℂ (Fin n)) = U x := fun _ => rfl
  have hWsurj : Function.Surjective W := by
    intro t
    obtain ⟨w, hw, hwt⟩ := hTL t t.2
    exact ⟨⟨w, hw⟩, Subtype.ext hwt⟩
  have hfin : finrank ℂ L = finrank ℂ T :=
    (LinearEquiv.ofBijective W.toLinearMap ⟨W.injective, hWsurj⟩).finrank_eq
  have hJ : ∀ π : Fin m → Fin n → ℂ, tangentJac (matSub U π) L = tangentJac π T := by
    intro π
    have hcomp : (linProjₗ (matSub U π)).comp L.subtype =
        ((linProjₗ π).comp T.subtype).comp W.toLinearMap := by
      refine LinearMap.ext fun x => ?_
      simp only [LinearMap.comp_apply, Submodule.subtype_apply, LinearIsometry.coe_toLinearMap,
        hWx]
      exact linProj_matSub U π x
    unfold tangentJac
    have h2 := LinearMap.normDet_comp_of_finrank_eq (𝕜 := ℂ) (U := L) (V := T)
      (W := EuclideanSpace ℂ (Fin m)) W.toLinearMap ((linProjₗ π).comp T.subtype) (by exact hfin)
    rw [hcomp, h2, LinearIsometry.normDet_eq_one, mul_one]
  have hemb : MeasurableEmbedding (matSub (m := m) U) := (matSubEquiv U).measurableEmbedding
  have key := (measurePreserving_matSub (m := m) U).lintegral_comp_emb hemb
    (fun π => matGauss π *
      (Metric.ball (0 : EuclideanSpace ℂ (Fin m)) 1).indicator 1
        (linProj π (((‖y‖ : ℝ) : ℂ) • firstCoordVec n)) *
      ENNReal.ofReal (tangentJac π (leadCoordPlane n m)))
  unfold tangentGaussProfile
  refine Eq.trans ?_ key
  refine lintegral_congr fun π => ?_
  simp only [matGauss_matSub, linProj_matSub, hUy, ← hL, hJ]

end

end GroundTheory.Heights₂.Heights
