import Mathlib
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.HeckeCharacterParameters
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SameBlockOfPosC
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemOfIsometryEigenOfDenseISup
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts MeasureTheory
open Formalism.MainNotions.SchurIrreducible (IrrU IrrGK IsHCMod)
open scoped TensorProduct

namespace GlobalTheory

theorem irrU_of_dense_graded_irrGK :
    ∀ (p q : ℕ) (T : GrpData p q) (σ : URep T) (M : GKMod p q) (j : M.V →ₗ[ℂ] σ.H), Function.Injective j → Dense (Set.range j) → (∀ Y ∈ upq p q, ∀ x, HasDerivAt (fun t : ℝ => σ.π (T.expt (t • Y)) (j x)) (j (M.act Y x)) 0) → IrrGK M → ∀ (N : ℕ → Submodule ℂ M.V) (k : T.G) (lam : ℕ → ℂ), (∀ m, FiniteDimensional ℂ (N m)) → (⨆ m, N m) = ⊤ → k ∈ T.Kset → Function.Injective lam → (∀ m, ∀ x ∈ N m, σ.π k (j x) = lam m • j x) → IrrU σ := by
  intro p q T σ M j hinj hd hder hirr N k lam hfin hN _ hlam heig
  haveI := hirr.1
  refine ⟨hinj.nontrivial, fun S hS hinv => ?_⟩
  haveI : CompleteSpace S := hS.completeSpace_coe
  have hreal : ∀ Y ∈ upq p q, ∀ y, j y ∈ S → j (M.act Y y) ∈ S := by
    intro Y hY y hy
    rw [← S.orthogonal_orthogonal, Submodule.mem_orthogonal]
    intro w hw
    have h1 := ((innerSL ℂ w).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hder Y hY y)
    have h2 : HasDerivAt (fun _ : ℝ => (0 : ℂ)) (inner ℂ w (j (M.act Y y))) 0 := by
      refine HasDerivAt.congr_of_eventuallyEq h1 (Filter.Eventually.of_forall fun t => ?_)
      exact (Submodule.inner_left_of_mem_orthogonal (hinv _ _ hy) hw).symm
    exact h2.unique (hasDerivAt_const _ _)
  have hstab : ∀ Z, ∀ y ∈ S.comap j, M.act Z y ∈ S.comap j := by
    intro Z y hy
    obtain ⟨X, hX, Y, hY, rfl⟩ := GlobalTheory.FockTensor.exists_upq_add Z
    rw [Submodule.mem_comap] at hy ⊢
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply]
    exact S.add_mem (hreal X hX y hy) (S.smul_mem _ (hreal Y hY y hy))
  rcases hirr.2 _ hstab with h | h
  · left
    have hperp : ∀ b ∈ Sᗮ, σ.π k b ∈ Sᗮ := by
      intro b hb
      rw [Submodule.mem_orthogonal']
      intro u hu
      rw [GlobalTheory.FockTensor.inner_pi_left]
      exact Submodule.inner_left_of_mem_orthogonal (hinv _ _ hu) hb
    have hdense : Dense ((⨆ m, (N m).map j : Submodule ℂ σ.H) : Set σ.H) := by
      rw [← Submodule.map_iSup, hN, Submodule.map_top]
      exact hd
    have hle : (⨆ m, (N m).map j : Submodule ℂ σ.H) ≤ Sᗮ := by
      refine iSup_le fun m => ?_
      rintro _ ⟨x, hx, rfl⟩
      obtain ⟨a, ha, b, hb, hab⟩ := S.exists_add_mem_mem_orthogonal (j x)
      have he := heig m x hx
      rw [hab, map_add, smul_add] at he
      have hdiff : σ.π k a - lam m • a = lam m • b - σ.π k b := by
        rw [sub_eq_sub_iff_add_eq_add, he, add_comm]
      have h1 : σ.π k a - lam m • a ∈ S := S.sub_mem (hinv _ _ ha) (S.smul_mem _ ha)
      have h2 : σ.π k a - lam m • a ∈ Sᗮ := by
        rw [hdiff]
        exact Sᗮ.sub_mem (Sᗮ.smul_mem _ hb) (hperp b hb)
      have h3 : σ.π k a = lam m • a :=
        sub_eq_zero.1 (inner_self_eq_zero.1 (Submodule.inner_right_of_mem_orthogonal h1 h2))
      have h4 := GlobalTheory.mem_of_isometry_eigen_of_dense_iSup σ.H (σ.π k) (σ.isom k)
        (fun m => (N m).map j) lam hlam (fun m => by haveI := hfin m; infer_instance)
        (by rintro m _ ⟨x, hx, rfl⟩; exact heig m x hx) hdense m a h3
      obtain ⟨x', -, hx'⟩ := h4
      have h5 : x' ∈ S.comap j := by rw [Submodule.mem_comap, hx']; exact ha
      rw [h, Submodule.mem_bot] at h5
      rw [h5, map_zero] at hx'
      rw [hab, ← hx', zero_add]
      exact hb
    rw [← Submodule.orthogonal_eq_top_iff, eq_top_iff]
    intro v _
    exact closure_minimal hle S.isClosed_orthogonal (hdense v)
  · right
    rw [eq_top_iff]
    intro v _
    refine closure_minimal ?_ hS (hd v)
    rintro _ ⟨x, rfl⟩
    have : x ∈ S.comap j := by rw [h]; trivial
    exact this

end GlobalTheory
