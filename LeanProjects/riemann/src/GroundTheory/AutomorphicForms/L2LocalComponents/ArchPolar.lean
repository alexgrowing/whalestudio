import Mathlib
import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.GKStableCartan
import GroundTheory.AutomorphicForms.RealGroupsPolar

open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace Matrix
open scoped NumberField.AdeleRing

namespace GroundTheory.Automorphic

noncomputable section

namespace AutomorphicForm

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

open Reduction in

theorem mem_archCompact_of_unitary (x : archGroup K n)
    (hr : ∀ v : {w : InfinitePlace K // IsReal w},
      realCompM v ((x : (ArchMatrix K n)ˣ) : ArchMatrix K n) ∈ unitaryGroup (Fin n) ℝ)
    (hc : ∀ v : {w : InfinitePlace K // IsComplex w},
      complexCompM v ((x : (ArchMatrix K n)ˣ) : ArchMatrix K n) ∈ unitaryGroup (Fin n) ℂ) :
    x ∈ archCompact K n := by
  show infEmb K n x ∈ Reduction.maxCompact (K := K) (n := n)
  refine ⟨fun w => ?_, fun v => ?_⟩
  · intro y
    by_cases hw : w.IsReal
    · set ψ := InfinitePlace.Completion.extensionEmbeddingOfIsReal hw
      have hψ : ∀ z, ‖ψ z‖ = ‖z‖ := fun z =>
        (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hw).norm_map_of_map_zero
          (map_zero _) z
      have hU := hr ⟨w, hw⟩
      rw [← euclidNorm_map ψ hψ, ← euclidNorm_map ψ hψ y]
      have e : (fun i => ψ ((y ᵥ* (infAt w (infEmb K n x) :
          Matrix (Fin n) (Fin n) w.Completion)) i)) =
          (fun i => ψ (y i)) ᵥ* realCompM ⟨w, hw⟩ ((x : (ArchMatrix K n)ˣ) : ArchMatrix K n) := by
        ext j
        simp only [vecMul, dotProduct, map_sum, map_mul, realCompM_apply, Matrix.map_apply,
          realComp_apply]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [infAt_infEmb_apply, extensionEmbeddingOfIsReal_symm]
      rw [e, euclidNorm_vecMul_unitary hU]
    · have hcw := InfinitePlace.not_isReal_iff_isComplex.1 hw
      set ψ := InfinitePlace.Completion.extensionEmbedding w
      have hψ : ∀ z, ‖ψ z‖ = ‖z‖ := fun z =>
        (InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero
          (map_zero _) z
      have hU := hc ⟨w, hcw⟩
      rw [← euclidNorm_map ψ hψ, ← euclidNorm_map ψ hψ y]
      have e : (fun i => ψ ((y ᵥ* (infAt w (infEmb K n x) :
          Matrix (Fin n) (Fin n) w.Completion)) i)) =
          (fun i => ψ (y i)) ᵥ* complexCompM ⟨w, hcw⟩ ((x : (ArchMatrix K n)ˣ) : ArchMatrix K n) := by
        ext j
        simp only [vecMul, dotProduct, map_sum, map_mul, complexCompM_apply, Matrix.map_apply,
          complexComp_apply]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [infAt_infEmb_apply, extensionEmbedding_symm _ hcw]
      rw [e, euclidNorm_vecMul_unitary hU]
  · have : finAt v (infEmb K n x) = 1 := by
      show (AdelicGLn.finiteRestrictedEquiv K n (AdelicGLn.prodEquiv K n (infEmb K n x)).2) v = 1
      rw [prodEquiv_infEmb, map_one]
      rfl
    rw [this]
    exact one_mem _

def archMatOfComps (Yr : {w : InfinitePlace K // IsReal w} → Matrix (Fin n) (Fin n) ℝ)
    (Yc : {w : InfinitePlace K // IsComplex w} → Matrix (Fin n) (Fin n) ℂ) : ArchMatrix K n :=
  show Matrix (Fin n) (Fin n) (mixedSpace K) from
    Matrix.of fun i j => ((fun v => Yr v i j), (fun v => Yc v i j))

@[simp] theorem realCompM_archMatOfComps (Yr : {w : InfinitePlace K // IsReal w} → Matrix (Fin n) (Fin n) ℝ)
    (Yc : {w : InfinitePlace K // IsComplex w} → Matrix (Fin n) (Fin n) ℂ)
    (v : {w : InfinitePlace K // IsReal w}) : realCompM v (archMatOfComps Yr Yc) = Yr v := by
  ext i j
  rfl

@[simp] theorem complexCompM_archMatOfComps
    (Yr : {w : InfinitePlace K // IsReal w} → Matrix (Fin n) (Fin n) ℝ)
    (Yc : {w : InfinitePlace K // IsComplex w} → Matrix (Fin n) (Fin n) ℂ)
    (v : {w : InfinitePlace K // IsComplex w}) : complexCompM v (archMatOfComps Yr Yc) = Yc v := by
  ext i j
  rfl

theorem exists_mem_archCompact_mul_expG (a : archGroup K n) :
    ∃ k ∈ archCompact K n, ∃ Y : archLie K n, a = k * (isExpLieAlgebra K n).expG Y := by
  set A : (ArchMatrix K n)ˣ := (a : (ArchMatrix K n)ˣ)
  set gr : ∀ v : {w : InfinitePlace K // IsReal w}, GL (Fin n) ℝ :=
    fun v => Units.map (realCompM (n := n) v).toMonoidHom A
  set gc : ∀ v : {w : InfinitePlace K // IsComplex w}, GL (Fin n) ℂ :=
    fun v => Units.map (complexCompM (n := n) v).toMonoidHom A
  set kr := fun v => polarExpHomeomorphReal.symm (gr v)
  set kc := fun v => polarExpHomeomorphComplex.symm (gc v)
  have hr : ∀ v, ((gr v : GL (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ) =
      ((kr v).1 : Matrix (Fin n) (Fin n) ℝ) * NormedSpace.exp (kr v).2.1 := fun v => by
    rw [← coe_polarExpHomeomorphReal_apply, Homeomorph.apply_symm_apply]
  have hc : ∀ v, ((gc v : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) =
      ((kc v).1 : Matrix (Fin n) (Fin n) ℂ) * NormedSpace.exp (kc v).2.1 := fun v => by
    rw [← coe_polarExpHomeomorphComplex_apply, Homeomorph.apply_symm_apply]
  set Y : archLie K n := ⟨archMatOfComps (fun v => (kr v).2.1) (fun v => (kc v).2.1), Submodule.mem_top⟩
  set E := (isExpLieAlgebra K n).expG Y
  have hE : ((E : (ArchMatrix K n)ˣ) : ArchMatrix K n) = NormedSpace.exp (Y : ArchMatrix K n) :=
    IsExpLieAlgebra.coe_expG _ Y
  refine ⟨a * E⁻¹, ?_, Y, (inv_mul_cancel_right a E).symm⟩
  apply mem_archCompact_of_unitary
  · intro v
    have e1 : realCompM v (((a * E⁻¹ : archGroup K n) : (ArchMatrix K n)ˣ) : ArchMatrix K n) =
        ((gr v : GL (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ) *
          ((Units.map (realCompM (n := n) v).toMonoidHom (E : (ArchMatrix K n)ˣ))⁻¹ :
            GL (Fin n) ℝ) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, map_mul]
      rfl
    have e2 : ((Units.map (realCompM (n := n) v).toMonoidHom (E : (ArchMatrix K n)ˣ) : GL (Fin n) ℝ) :
        Matrix (Fin n) (Fin n) ℝ) = NormedSpace.exp (kr v).2.1 := by
      show realCompM v ((E : (ArchMatrix K n)ˣ) : ArchMatrix K n) = _
      rw [hE, realCompM_exp]
      exact congrArg _ (realCompM_archMatOfComps _ _ v)
    rw [e1, hr]
    have e3 : ((kr v).1 : Matrix (Fin n) (Fin n) ℝ) * NormedSpace.exp (kr v).2.1 *
        (((Units.map (realCompM (n := n) v).toMonoidHom (E : (ArchMatrix K n)ˣ))⁻¹ : GL (Fin n) ℝ) :
          Matrix (Fin n) (Fin n) ℝ) = (kr v).1 := by
      rw [← e2, Units.mul_inv_cancel_right]
    rw [e3]
    exact (kr v).1.2
  · intro v
    have e1 : complexCompM v (((a * E⁻¹ : archGroup K n) : (ArchMatrix K n)ˣ) : ArchMatrix K n) =
        ((gc v : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) *
          ((Units.map (complexCompM (n := n) v).toMonoidHom (E : (ArchMatrix K n)ˣ))⁻¹ :
            GL (Fin n) ℂ) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, map_mul]
      rfl
    have e2 : ((Units.map (complexCompM (n := n) v).toMonoidHom (E : (ArchMatrix K n)ˣ) :
        GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) = NormedSpace.exp (kc v).2.1 := by
      show complexCompM v ((E : (ArchMatrix K n)ˣ) : ArchMatrix K n) = _
      rw [hE, complexCompM_exp]
      exact congrArg _ (complexCompM_archMatOfComps _ _ v)
    rw [e1, hc]
    have e3 : ((kc v).1 : Matrix (Fin n) (Fin n) ℂ) * NormedSpace.exp (kc v).2.1 *
        (((Units.map (complexCompM (n := n) v).toMonoidHom (E : (ArchMatrix K n)ˣ))⁻¹ :
          GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) = (kc v).1 := by
      rw [← e2, Units.mul_inv_cancel_right]
    rw [e3]
    exact (kc v).1.2

end AutomorphicForm

end

end GroundTheory.Automorphic
