import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixExtendByZeroAdd
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.AdaptEv

noncomputable section

namespace GlobalTheory.ThK.AdaptEv.Restr

theorem extendByZeroOffSubset_smul_apply {κ ι κ₁ R S : Type} [Zero R] [SMulZeroClass S R] (eq : κ ≃ ι ⊕ κ₁) (c : S) (a : κ₁ → R) :
    ext0 eq (c • a) = c • ext0 eq a := by
  funext k; simp only [ext0, Pi.smul_apply]; cases eq k <;> simp

theorem matrixExtendByZero_zero {κ ι κ₁ R : Type} [Zero R] (eq : κ ≃ ι ⊕ κ₁) : ext0 eq (0 : κ₁ → R) = 0 := by
  funext k; simp only [ext0]; cases eq k <;> rfl

open scoped Classical

variable (F : Type) [Field F] [NumberField F]

def extendByZeroCLM' {κ ι κ₁ : Type} [Fintype κ] [Fintype κ₁] (eq : κ ≃ ι ⊕ κ₁) :
    (κ₁ → mixedEmbedding.mixedSpace F) →L[ℝ] (κ → mixedEmbedding.mixedSpace F) :=
  LinearMap.toContinuousLinearMap
    { toFun := ext0 eq
      map_add' := matrixExtendByZero_add eq
      map_smul' := fun c x => extendByZeroOffSubset_smul_apply eq c x }

theorem extend_by_zero_linear_apply {κ ι κ₁ : Type} [Fintype κ] [Fintype κ₁] (eq : κ ≃ ι ⊕ κ₁)
    (x : κ₁ → mixedEmbedding.mixedSpace F) : extendByZeroCLM' F eq x = ext0 eq x := rfl

theorem norm_le_norm_extend_by_zero {κ ι κ₁ : Type} [Fintype κ] [Fintype κ₁] (eq : κ ≃ ι ⊕ κ₁)
    (x : κ₁ → mixedEmbedding.mixedSpace F) : ‖x‖ ≤ ‖ext0 eq x‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun p => ?_
  have := norm_le_pi_norm (ext0 eq x) (eq.symm (Sum.inr p))
  rwa [ext0_inr] at this

def restrS {κ ι κ₁ : Type} [Fintype κ] [Fintype κ₁] (eq : κ ≃ ι ⊕ κ₁) : SInf F κ →L[ℂ] SInf F κ₁ :=
  SchwartzMap.compCLM ℂ (extendByZeroCLM' F eq).hasTemperateGrowth
    ⟨1, 1, fun x => by
      have := norm_le_norm_extend_by_zero F eq x
      simp only [extend_by_zero_linear_apply, pow_one, one_mul]
      linarith [norm_nonneg (ext0 eq x)]⟩

theorem restrS_apply {κ ι κ₁ : Type} [Fintype κ] [Fintype κ₁] (eq : κ ≃ ι ⊕ κ₁) (f : SInf F κ)
    (y : κ₁ → mixedEmbedding.mixedSpace F) : restrS F eq f y = f (ext0 eq y) := rfl

theorem restrS_ne_zero {κ ι κ₁ : Type} [Fintype κ] [Fintype κ₁] (eq : κ ≃ ι ⊕ κ₁) : restrS F eq ≠ 0 := by
  classical
  intro h
  let b : ContDiffBump (0 : κ → mixedEmbedding.mixedSpace F) := ⟨1, 2, one_pos, one_lt_two⟩
  have hs : HasCompactSupport (fun x => ((b x : ℝ) : ℂ)) :=
    b.hasCompactSupport.comp_left (g := fun t : ℝ => (t : ℂ)) (by simp)
  have hc : ContDiff ℝ (⊤ : ℕ∞) (fun x => ((b x : ℝ) : ℂ)) := Complex.ofRealCLM.contDiff.comp b.contDiff
  have h1 := congrArg (fun T : SInf F κ →L[ℂ] SInf F κ₁ => T (hs.toSchwartzMap hc) 0) h
  have h2 : b 0 = 1 := b.one_of_mem_closedBall (by simp [b])
  simp only [restrS_apply, matrixExtendByZero_zero, ContinuousLinearMap.zero_apply, SchwartzMap.zero_apply] at h1
  change ((b 0 : ℝ) : ℂ) = 0 at h1
  simp [h2] at h1

end GlobalTheory.ThK.AdaptEv.Restr

theorem GlobalTheory.ThK.AdaptEv.exists_restr_schwartz :
    ∀ (F : Type) [Field F] [NumberField F] {κ ι κ₁ : Type} [Fintype κ] [Fintype ι] [Fintype κ₁] (eq : κ ≃ ι ⊕ κ₁),
    ∃ ei : SInf F κ →L[ℂ] SInf F κ₁, ei ≠ 0 ∧ ∀ f y, ei f y = f (ext0 eq y) := by
  intro F _ _ κ ι κ₁ _ _ _ eq
  exact ⟨Restr.restrS F eq, Restr.restrS_ne_zero F eq, fun f y => rfl⟩
