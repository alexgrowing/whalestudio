import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthogonalGaussModels.HermitianBlockFrames.ExistsUnitVec

noncomputable section
open scoped BigOperators
open Matrix

namespace Formalism.L2.Th1.Top.FrP.UnitaryGroupMassFormula.HermFrame.Jac
namespace JSetup

variable {K : Type*} [Field K] (S : JSetup K)
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def Γp (Γ : Matrix ι ι K) (a : ι → K) : Matrix ι ι K := Γ - vecMulVec (Γ *ᵥ a) (S.cv a ᵥ* Γ)

def proj (Γ : Matrix ι ι K) (a y : ι → K) : ι → K := y - S.hf Γ a y • a

theorem hf_eq_vecMul (Γ : Matrix ι ι K) (x y : ι → K) : S.hf Γ x y = (S.cv x ᵥ* Γ) ⬝ᵥ y :=
  dotProduct_mulVec _ _ _

private theorem vecMulVec_mulVec_hermitian_block_frames (u v y : ι → K) : vecMulVec u v *ᵥ y = (v ⬝ᵥ y) • u := by
  ext i
  simp only [mulVec, dotProduct, vecMulVec_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem Γp_mulVec (Γ : Matrix ι ι K) (a y : ι → K) :
    S.Γp Γ a *ᵥ y = Γ *ᵥ y - S.hf Γ a y • (Γ *ᵥ a) := by
  rw [Γp, sub_mulVec, vecMulVec_mulVec_hermitian_block_frames, hf_eq_vecMul]

private theorem vecMul_vecMulVec' (u v x : ι → K) : x ᵥ* vecMulVec u v = (x ⬝ᵥ u) • v := by
  ext j
  simp only [vecMul, dotProduct, vecMulVec_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem vecMul_Γp (Γ : Matrix ι ι K) (a x : ι → K) :
    S.cv x ᵥ* S.Γp Γ a = S.cv x ᵥ* Γ - S.hf Γ x a • (S.cv a ᵥ* Γ) := by
  rw [Γp, vecMul_sub, vecMul_vecMulVec']
  rfl

theorem hf_Γp (Γ : Matrix ι ι K) (a x y : ι → K) :
    S.hf (S.Γp Γ a) x y = S.hf Γ x y - S.hf Γ a y * S.hf Γ x a := by
  show S.cv x ⬝ᵥ (S.Γp Γ a *ᵥ y) = _
  rw [Γp_mulVec, dotProduct_sub, dotProduct_smul, smul_eq_mul]
  rfl

variable {Γ : Matrix ι ι K} {a : ι → K}

theorem Γp_mulVec_self (haa : S.hf Γ a a = 1) : S.Γp Γ a *ᵥ a = 0 := by
  rw [Γp_mulVec, haa, one_smul, sub_self]

theorem vecMul_Γp_self (haa : S.hf Γ a a = 1) : S.cv a ᵥ* S.Γp Γ a = 0 := by
  rw [vecMul_Γp, haa, one_smul, sub_self]

theorem IntM_Γp (hΓ : S.IntM Γ) (ha : S.IntV a) : S.IntM (S.Γp Γ a) := by
  intro i j
  have h1 : (Γ *ᵥ a) i ∈ S.O := S.IntV_mulVec hΓ ha i
  have h2 : (S.cv a ᵥ* Γ) j ∈ S.O := by
    simp only [vecMul, dotProduct]
    exact S.O.sum_mem fun k _ => S.O.mul_mem (S.IntV_cv ha k) (hΓ k j)
  simp only [Γp, Matrix.sub_apply, vecMulVec_apply]
  exact S.O.sub_mem (hΓ i j) (S.O.mul_mem h1 h2)

theorem Herm_Γp (hΓ : S.IntM Γ) (hH : S.Herm Γ) (ha : S.IntV a) : S.Herm (S.Γp Γ a) := by
  intro i j
  simp only [Γp, Matrix.sub_apply, vecMulVec_apply, map_sub, map_mul, hH i j, S.σ_mulVec hH,
    S.σ_vecMul hH ha]
  ring

theorem mulVec_proj (Γ : Matrix ι ι K) (a y : ι → K) : Γ *ᵥ S.proj Γ a y = S.Γp Γ a *ᵥ y := by
  rw [proj, mulVec_sub, mulVec_smul, Γp_mulVec]

theorem IntV_proj (hΓ : S.IntM Γ) (ha : S.IntV a) {y : ι → K} (hy : S.IntV y) : S.IntV (S.proj Γ a y) :=
  S.IntV_sub hy (S.IntV_smul (S.hf_mem hΓ ha hy) ha)

private theorem sub_smul_vecMul (x b : ι → K) (c : K) (M : Matrix ι ι K) :
    (x - c • b) ᵥ* M = x ᵥ* M - c • (b ᵥ* M) := by
  ext j
  simp only [vecMul, dotProduct, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, sub_mul,
    Finset.sum_sub_distrib, Finset.mul_sum, mul_assoc]

private theorem hf_proj_right_eq_hf_Γp (Γ : Matrix ι ι K) (a x y : ι → K) :
    S.hf Γ x (S.proj Γ a y) = S.hf (S.Γp Γ a) x y := by
  show S.cv x ⬝ᵥ (Γ *ᵥ S.proj Γ a y) = S.cv x ⬝ᵥ (S.Γp Γ a *ᵥ y)
  rw [mulVec_proj]

theorem hf_proj_proj (haa : S.hf Γ a a = 1) (x y : ι → K) :
    S.hf Γ (S.proj Γ a x) (S.proj Γ a y) = S.hf (S.Γp Γ a) x y := by
  rw [hf_proj_right_eq_hf_Γp, hf_eq_vecMul, hf_eq_vecMul, proj, cv_sub, cv_smul,
    sub_smul_vecMul, S.vecMul_Γp_self haa, smul_zero, sub_zero]

theorem hf_self_proj (haa : S.hf Γ a a = 1) (y : ι → K) : S.hf Γ a (S.proj Γ a y) = 0 := by
  rw [hf_proj_right_eq_hf_Γp, hf_Γp, haa, mul_one, sub_self]

theorem hf_proj_self (hΓ : S.IntM Γ) (hH : S.Herm Γ) (ha : S.IntV a) (haa : S.hf Γ a a = 1) {y : ι → K}
    (hy : S.IntV y) : S.hf Γ (S.proj Γ a y) a = 0 := by
  rw [S.hf_swap hΓ hH ha (S.IntV_proj hΓ ha hy), S.hf_self_proj haa, map_zero]

theorem vecMul_proj (hΓ : S.IntM Γ) (hH : S.Herm Γ) (ha : S.IntV a) {y : ι → K} (hy : S.IntV y) :
    S.cv (S.proj Γ a y) ᵥ* Γ = S.cv y ᵥ* S.Γp Γ a := by
  rw [proj, cv_sub, cv_smul, sub_smul_vecMul, vecMul_Γp, S.hf_swap hΓ hH ha hy]

theorem UM_Γp (hΓ : S.IntM Γ) (hH : S.Herm Γ) (hU : S.UM Γ) (ha : S.IntV a) (haa : S.hf Γ a a = 1) :
    S.UM (S.Γp Γ a) := by
  intro x hx hPx
  have hz := S.IntV_proj hΓ ha hx
  have hΓz : ∀ i, S.NU ((Γ *ᵥ S.proj Γ a x) i) := by
    intro i
    rw [mulVec_proj]
    exact hPx i
  obtain ⟨z, hz', hzz⟩ := hU _ hz hΓz
  refine ⟨z, hz', ?_⟩
  have h0 : S.hf Γ a z = 0 := by
    have h1 : S.hf Γ a (S.proj Γ a x) = S.p * S.hf Γ a z := by
      show S.cv a ⬝ᵥ (Γ *ᵥ S.proj Γ a x) = S.p * (S.cv a ⬝ᵥ (Γ *ᵥ z))
      rw [hzz, dotProduct_smul, smul_eq_mul]
    rw [S.hf_self_proj haa] at h1
    exact (mul_eq_zero.mp h1.symm).resolve_left S.hp0
  rw [← S.mulVec_proj Γ a x, hzz, Γp_mulVec, h0, zero_smul, sub_zero]

end JSetup
end Formalism.L2.Th1.Top.FrP.UnitaryGroupMassFormula.HermFrame.Jac
