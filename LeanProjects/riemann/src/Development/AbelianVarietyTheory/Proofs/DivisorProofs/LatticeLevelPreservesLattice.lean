import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMaxThOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemFinPt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TruncMatTranspose
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemLatLevel
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

open scoped Matrix

namespace GlobalTheory.ThKLevelLat

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n d : ℕ}

omit [NumberField E] in

theorem smul_incM_vecMulVec (a : AF F) (x : Fin n → E) (y : Fin d → E) :
    a • incM F (Matrix.vecMulVec x y) =
      Matrix.vecMulVec (fun i => inclR (AF F) (x i)) (a • fun j => inclR (AF F) (y j)) := by
  ext i j
  simp only [incM, Matrix.smul_apply, Matrix.map_apply, Matrix.vecMulVec_apply, Pi.smul_apply, map_mul,
    mul_smul_comm]

omit [NumberField E] in

theorem vecMulVec_mem (V : Spc F E n) (W : Spc F E d) (w : Pl F) {x : Fin n → E} (hx : x ∈ V.L) :
    ∀ z ∈ GlobalTheory.InertSph.latAt W w, Matrix.vecMulVec (fun i => inclR (AF F) (x i)) z ∈ latAtV V W w := by
  intro z hz
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, hint, y, hy, rfl⟩ := hz
    rw [← smul_incM_vecMulVec]
    exact AddSubgroup.subset_closure ⟨a, ha, hint, x, hx, y, hy, rfl⟩
  | zero =>
    have h0 : Matrix.vecMulVec (fun i => inclR (AF F) (x i)) (0 : Fin d → AE F E) = 0 := by
      ext i j
      exact mul_zero _
    rw [h0]
    exact zero_mem _
  | add u v _ _ hu hv => rw [Matrix.vecMulVec_add]; exact add_mem hu hv
  | neg u _ hu => rw [Matrix.vecMulVec_neg]; exact neg_mem hu

omit [NumberField E] in

theorem mul_transpose_mem (V : Spc F E n) (W : Spc F E d) (w : Pl F) (N : Matrix (Fin d) (Fin d) (AE F E))
    (hN : ∀ z ∈ GlobalTheory.InertSph.latAt W w, N *ᵥ z ∈ GlobalTheory.InertSph.latAt W w) :
    ∀ γ ∈ latAtV V W w, γ * Nᵀ ∈ latAtV V W w := by
  intro γ hγ
  induction hγ using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, hint, x, hx, y, hy, rfl⟩ := hz
    rw [smul_incM_vecMulVec, Matrix.vecMulVec_mul, Matrix.vecMul_transpose]
    exact vecMulVec_mem V W w hx _ (hN _ (AddSubgroup.subset_closure ⟨a, ha, hint, y, hy, rfl⟩))
  | zero => rw [Matrix.zero_mul]; exact zero_mem _
  | add u v _ _ hu hv => rw [Matrix.add_mul]; exact add_mem hu hv
  | neg u _ hu => rw [Matrix.neg_mul]; exact neg_mem hu

theorem mul_transpose_mem_iff : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n d : ℕ) (V : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n) (W : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d) (k : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ W.J), k ∈ GlobalTheory.ThKLevel.latLevel σ W → ∀ (w : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) (γ : Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E)), γ * Matrix.transpose (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat k) ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV V W w ↔ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV V W w := by
  intro F E _ _ _ _ _ σ n d V W k hk w γ
  have hk' := (GlobalTheory.ThKLevel.mem_latLevel.1 hk).2 w
  refine ⟨fun h => ?_, mul_transpose_mem V W w _ (fun z hz => (hk' z hz).1) γ⟩
  have h1 := mul_transpose_mem V W w _ (fun z hz => (hk' z hz).2) _ h
  rwa [Matrix.mul_assoc, ← Matrix.transpose_mul, show mat k⁻¹ * mat k = mat (k⁻¹ * k) from rfl, inv_mul_cancel,
    show mat (1 : UA σ W.J) = 1 from rfl, Matrix.transpose_one, Matrix.mul_one] at h1

end GlobalTheory.ThKLevelLat

end
