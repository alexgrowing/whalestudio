import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthogonalGaussModels.HermitianBlockFrames.TransposeMulBlockDiagMul
import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthogonalGaussModels.HermitianBlockFrames.CardEqOfMulEqOne

noncomputable section
open scoped BigOperators
open Matrix

namespace Formalism.L2.Th1.Top.FrP.UnitaryGroupMassFormula.HermFrame.Loc
open Formalism.L2.Th1.Top.FrP Jac

set_option maxHeartbeats 400000 in
theorem local_core' : LocCore := by
  intro l _ dK σ δ h5 hld hin hσ hδ hσδ n _ _ M₁ M₂ R₁ R₂ c hc hGram hmv
  set S := setup h5 dK hld hin σ hσ δ hδ hσδ with hS
  have hSσ : S.σ = σ := rfl
  set M := lmat δ M₁ M₂ with hM
  set Mb := lmat δ M₁ (-M₂) with hMb
  have hMσ : M.map σ = Mb := lmat_map_σ σ δ hσδ M₁ M₂
  have hMbσ : Mb.map σ = M := by rw [hMb, lmat_map_σ σ δ hσδ, neg_neg]
  have hc0 : (c : MaximalUnramifiedExtension l) ≠ 0 := by
    have : c ≠ 0 := by rintro rfl; simp at hc
    exact_mod_cast this
  set H₀ : Matrix n n (MaximalUnramifiedExtension l) := (c : MaximalUnramifiedExtension l)⁻¹ • (lmat δ R₁ R₂).map σ with hH₀

  have hE : Mbᵀ * bd4 H₀ * M = 1 := by
    have h1 := congrArg (fun X => X.map σ) hGram
    simp only [Matrix.map_mul, transpose_map, blockDiag_map', hMσ, hMbσ] at h1
    have h1' : ((c : MaximalUnramifiedExtension l) • (1 : Matrix (Fin 4 × n) (Fin 4 × n) (MaximalUnramifiedExtension l))).map σ = (c : MaximalUnramifiedExtension l) • 1 := by
      refine Matrix.ext fun x y => ?_
      simp only [Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
      split_ifs <;> simp
    rw [h1'] at h1
    rw [hH₀, bd4_smul, Matrix.mul_smul, Matrix.smul_mul, h1, smul_smul, inv_mul_cancel₀ hc0, one_smul]
  have hE2 : Mbᵀ * bd4 (H₀.map σ)ᵀ * M = 1 := by
    have h1 := congrArg (fun X => (X.map σ)ᵀ) hE
    simp only [Matrix.map_mul, transpose_map, blockDiag_map', hMσ, hMbσ, transpose_mul, transpose_transpose,
      Matrix.map_one σ (map_zero σ) (map_one σ), transpose_one, bd4_transpose] at h1
    simpa [Matrix.mul_assoc] using h1

  set Z : Matrix n (Fin 4 × n) (MaximalUnramifiedExtension l) := what₂ M 0 with hZ
  set Zb : Matrix n (Fin 4 × n) (MaximalUnramifiedExtension l) := what₂ Mb 0 with hZb'
  have hZb : Z.map σ = Zb := Matrix.ext fun i w => congrFun (congrFun hMσ (0, i)) w
  have hZbσ : Zb.map σ = Z := Matrix.ext fun i w => congrFun (congrFun hMbσ (0, i)) w
  have hZZ : Z * (Zbᵀ * H₀) = 1 := by
    have h1 : M * (Mbᵀ * bd4 H₀) = 1 := mul_eq_one_comm.mp hE
    refine Matrix.ext fun i j => ?_
    have := congrFun (congrFun h1 (0, i)) (0, j)
    rw [← Matrix.mul_assoc, mul_bd4_apply] at this
    rw [← Matrix.mul_assoc, Matrix.mul_apply]
    simp only [Matrix.one_apply, Prod.mk.injEq, true_and] at this
    rw [Matrix.one_apply]
    simpa [Matrix.mul_apply, hZ, hZb', what₂] using this
  obtain ⟨Γ, hΓ⟩ : ∃ Γ : Matrix (Fin 4 × n) (Fin 4 × n) (MaximalUnramifiedExtension l), Γ = Zbᵀ * H₀ * Z := ⟨_, rfl⟩

  choose U₁ U₂ hUint hUeq using hmv
  set U : Fin 4 → Matrix (Fin 4 × n) (Fin 4 × n) (MaximalUnramifiedExtension l) := fun b => lmat δ (U₁ b) (U₂ b) with hU
  have hUO : ∀ b x y, U b x y ∈ S.O := fun b x y => lmat_mem (dK := dK) (hδ := hδ) (U₁ b) (U₂ b) (hUint b) x y
  have hZc : ∀ b, what₂ M b = Z * U b := by
    intro b; refine Matrix.ext fun i w => ?_
    have := congrFun (congrFun (hUeq b) (0, i)) w
    rw [blockShift_mul_apply, if_pos rfl] at this
    exact this
  have hrowsN : ∀ b, what₂ (M * U 0) b = if b = 0 then Z else 0 := by
    intro b; refine Matrix.ext fun i w => ?_
    have := congrFun (congrFun (hUeq 0) (b, i)) w
    rw [blockShift_mul_apply] at this
    rw [what₂, ← this]
    split_ifs <;> rfl
  have hΓU : Γ = ((U 0).map σ)ᵀ * U 0 := by
    have hN : ((M * U 0).map σ)ᵀ * bd4 H₀ * (M * U 0) = ((U 0).map σ)ᵀ * U 0 := by
      rw [Matrix.map_mul, hMσ, transpose_mul]
      calc ((U 0).map σ)ᵀ * Mbᵀ * bd4 H₀ * (M * U 0) = ((U 0).map σ)ᵀ * (Mbᵀ * bd4 H₀ * M) * U 0 := by
            simp only [Matrix.mul_assoc]
        _ = _ := by rw [hE, Matrix.mul_one]
    rw [← hN, transpose_mul_blockDiag_mul, Fin.sum_univ_four]
    have hr : ∀ b, what₂ ((M * U 0).map σ) b = (what₂ (M * U 0) b).map σ := fun b => rfl
    simp only [hr, hrowsN]
    simp [hZb, hΓ]
  have hΓI : S.IntM Γ := by
    intro w w'
    rw [hΓU, Matrix.mul_apply]
    exact S.O.sum_mem fun k _ => S.O.mul_mem (S.hσO _ (hUO 0 k w)) (hUO 0 k w')
  have hΓH : S.Herm Γ := by
    intro w w'
    rw [hΓU]
    simp only [hSσ, Matrix.mul_apply, transpose_apply, Matrix.map_apply, map_sum, map_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    have h := S.hσσ _ (hUO 0 k w)
    rw [hSσ] at h
    rw [h]
    ring
  have hidem : Γ * Γ = Γ := by
    calc Γ * Γ = Zbᵀ * H₀ * (Z * (Zbᵀ * H₀)) * Z := by simp only [hΓ, Matrix.mul_assoc]
      _ = Γ := by rw [hZZ, Matrix.mul_one, hΓ]
  have hΓUM : S.UM Γ := by
    intro x hx hNU
    choose y hyO hy using hNU
    refine ⟨y, hyO, ?_⟩
    have hΓx : Γ *ᵥ x = S.p • y := funext fun i => by rw [hy i]; rfl
    have h2 : Γ *ᵥ (Γ *ᵥ x) = Γ *ᵥ x := by rw [mulVec_mulVec, hidem]
    rw [hΓx, mulVec_smul] at h2
    rw [hΓx, h2]
  obtain ⟨k, v, hvI, hvo, hvs⟩ := S.jac Γ hΓI hΓH hΓUM
  clear_value Z Zb H₀ M Mb

  set A : Matrix (Fin 4 × n) (Fin k) (MaximalUnramifiedExtension l) := Matrix.of fun w c => v c w with hA
  have hAO : ∀ w c, A w c ∈ S.O := fun w c => hvI c w
  have hAo : (A.map σ)ᵀ * Γ * A = 1 := by
    refine Matrix.ext fun c c' => ?_
    rw [Matrix.one_apply, ← hvo c c']
    simp only [JSetup.hf, JSetup.cv, hSσ, dotProduct, mulVec, Matrix.mul_apply, transpose_apply,
      Matrix.map_apply, hA, Matrix.of_apply, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have hAs : Γ * A * ((A.map σ)ᵀ * Γ) = Γ := by
    conv_rhs => rw [← hvs]
    refine Matrix.ext fun w w' => ?_
    rw [Matrix.mul_apply, Matrix.sum_apply]
    refine Finset.sum_congr rfl fun c _ => ?_
    simp only [vecMulVec_apply, Matrix.mul_apply, mulVec, dotProduct, vecMul, JSetup.cv, hSσ, transpose_apply,
      Matrix.map_apply, hA, Matrix.of_apply]
  obtain ⟨V, hV⟩ : ∃ V : Matrix n (Fin k) (MaximalUnramifiedExtension l), V = Z * A := ⟨_, rfl⟩
  obtain ⟨Ti₀, hTi₀⟩ : ∃ Ti₀ : Matrix (Fin k) n (MaximalUnramifiedExtension l), Ti₀ = (V.map σ)ᵀ * H₀ := ⟨_, rfl⟩
  have hVσ : V.map σ = Zb * A.map σ := by rw [hV, Matrix.map_mul, hZb]
  have hTZ : Ti₀ * Z = (A.map σ)ᵀ * Γ := by
    rw [hTi₀, hVσ, transpose_mul, hΓ]; simp only [Matrix.mul_assoc]
  have hTV : Ti₀ * V = 1 := by
    rw [hV, ← Matrix.mul_assoc, hTZ, hAo]
  have hZΓ : Z * Γ = Z := by
    calc Z * Γ = Z * (Zbᵀ * H₀) * Z := by simp only [hΓ, Matrix.mul_assoc]
      _ = Z := by rw [hZZ, Matrix.one_mul]
  have hGZ : Zbᵀ * H₀ = Γ * (Zbᵀ * H₀) := by
    calc Zbᵀ * H₀ = Zbᵀ * H₀ * (Z * (Zbᵀ * H₀)) := by rw [hZZ, Matrix.mul_one]
      _ = Γ * (Zbᵀ * H₀) := by simp only [hΓ, Matrix.mul_assoc]
  have hTi₀' : Ti₀ = (A.map σ)ᵀ * (Zbᵀ * H₀) := by rw [hTi₀, hVσ, transpose_mul, Matrix.mul_assoc]
  have hVT : V * Ti₀ = 1 := by
    have s1 : V * Ti₀ = Z * A * ((A.map σ)ᵀ * (Zbᵀ * H₀)) := by rw [hV, hTi₀']
    have s2 : Z * A * ((A.map σ)ᵀ * (Zbᵀ * H₀)) = Z * Γ * A * ((A.map σ)ᵀ * (Γ * (Zbᵀ * H₀))) :=
      (congrArg (fun X => Z * A * ((A.map σ)ᵀ * X)) hGZ).trans
        (congrArg (fun X => X * A * ((A.map σ)ᵀ * (Γ * (Zbᵀ * H₀)))) hZΓ.symm)
    have s3 : Z * Γ * A * ((A.map σ)ᵀ * (Γ * (Zbᵀ * H₀))) = Z * (Γ * A * ((A.map σ)ᵀ * Γ)) * (Zbᵀ * H₀) := by
      simp only [Matrix.mul_assoc]
    have s4 : Z * (Γ * A * ((A.map σ)ᵀ * Γ)) * (Zbᵀ * H₀) = 1 := by rw [hAs, hZΓ, hZZ]
    exact s1.trans (s2.trans (s3.trans s4))

  have hk : Fintype.card n = k := card_eq_of_mul_eq_one V Ti₀ hVT hTV
  set e : Fin k ≃ n := (Fintype.equivFinOfCardEq hk).symm with he
  set T : Matrix n n (MaximalUnramifiedExtension l) := V.submatrix id e.symm with hT
  set Ti : Matrix n n (MaximalUnramifiedExtension l) := Ti₀.submatrix e.symm id with hTi
  have hTTi : T * Ti = 1 := by
    refine Matrix.ext fun i j => ?_
    have h1 := congrFun (congrFun hVT i) j
    rw [Matrix.mul_apply] at h1
    rw [← h1, Matrix.mul_apply]
    simp only [hT, hTi, submatrix_apply, id_eq]
    exact Equiv.sum_comp e.symm (fun c => V i c * Ti₀ c j)

  have hAσσ : (A.map σ).map σ = A := Matrix.ext fun w c => by
    have h := S.hσσ _ (hAO w c)
    rw [hSσ] at h
    simpa using h
  have hVσσ : (V.map σ).map σ = V := by rw [hVσ, Matrix.map_mul, hZbσ, hAσσ, hV]
  have hTi₀σ : (Ti₀.map σ)ᵀ * Ti₀ = (H₀.map σ)ᵀ := by
    have h1 : (Ti₀.map σ)ᵀ = (H₀.map σ)ᵀ * V := by
      rw [hTi₀, Matrix.map_mul, transpose_mul, transpose_map, transpose_transpose, hVσσ]
    rw [h1, Matrix.mul_assoc, hVT, Matrix.mul_one]
  have hTiσ : (Ti.map σ)ᵀ * Ti = (H₀.map σ)ᵀ := by
    rw [← hTi₀σ]
    refine Matrix.ext fun i j => ?_
    simp only [hTi, Matrix.mul_apply, transpose_apply, Matrix.map_apply, submatrix_apply, id_eq]
    exact Equiv.sum_comp e.symm (fun c => σ (Ti₀ c i) * Ti₀ c j)
  have hU1 : ((bd4 Ti * M).map σ)ᵀ * (bd4 Ti * M) = 1 := by
    rw [Matrix.map_mul, blockDiag_map', hMσ, transpose_mul, bd4_transpose]
    calc Mbᵀ * bd4 (Ti.map σ)ᵀ * (bd4 Ti * M) = Mbᵀ * (bd4 (Ti.map σ)ᵀ * bd4 Ti) * M := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [blockDiag_mul', hTiσ]; exact hE2

  have hγ : ∀ b i w, (bd4 Ti * M) (b, i) w = ((A.map σ)ᵀ * Γ * U b) (e.symm i) w := by
    intro b i w
    rw [blockDiag_mul_apply']
    have h1 : (Ti * what₂ M b) i w = ∑ j, Ti i j * M (b, j) w := rfl
    rw [← h1, hZc b, ← Matrix.mul_assoc, Matrix.mul_apply, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun w' _ => ?_
    congr 1
    show (Ti₀ * Z) (e.symm i) w' = _
    rw [hTZ]
  have hγO : ∀ x y, (bd4 Ti * M) x y ∈ S.O := by
    rintro ⟨b, i⟩ w
    rw [hγ, Matrix.mul_apply]
    refine S.O.sum_mem fun w' _ => S.O.mul_mem ?_ (hUO b w' w)
    rw [Matrix.mul_apply]
    refine S.O.sum_mem fun x _ => S.O.mul_mem ?_ (hΓI x w')
    have h := S.hσO _ (hAO x (e.symm i))
    rw [hSσ] at h
    simpa using h
  refine ⟨T, Ti, hTTi, ?_⟩
  unfold IsUnitaryK
  refine ⟨fun a b => ⟨norm_le_one_of_mem (dK := dK) (hδ := hδ) (hγO a b), ?_⟩, fun a b => ?_⟩
  · have h := S.hσσ _ (hγO a b)
    rwa [hSσ] at h
  · have h := congrFun (congrFun hU1 a) b
    rw [Matrix.mul_apply, Matrix.one_apply] at h
    simp only [transpose_apply, Matrix.map_apply] at h
    exact h

end Formalism.L2.Th1.Top.FrP.UnitaryGroupMassFormula.HermFrame.Loc
