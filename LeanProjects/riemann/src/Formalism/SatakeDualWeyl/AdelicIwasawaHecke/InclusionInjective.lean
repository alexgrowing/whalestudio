import Formalism.SatakeDualWeyl.Statement

noncomputable section

open Matrix TensorProduct

namespace Formalism.UG.P

open Formalism.UG

theorem bc_coe {A B : Type} [CommRing A] [CommRing B] {n : Type} [Fintype n] [DecidableEq n]
    (φ : A →+* B) (g : GL n A) : ((bc φ g : GL n B) : Matrix n n B) = (g : Matrix n n A).map φ :=
  rfl

theorem incl_cT_map {A B : Type} [CommRing A] [CommRing B] {m p : Type}
    (σ : A →+* A) (σ' : B →+* B) (φ : A →+* B) (h : φ.comp σ = σ'.comp φ) (M : Matrix m p A) :
    cT σ' (M.map φ) = (cT σ M).map φ := by
  ext i j
  simp only [Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply]
  exact (RingHom.congr_fun h (M j i)).symm

theorem bc_mem {A B : Type} [CommRing A] [CommRing B] {n : Type} [Fintype n] [DecidableEq n]
    (σ : A →+* A) (σ' : B →+* B) (φ : A →+* B) (h : φ.comp σ = σ'.comp φ)
    (J : Matrix n n A) (g : GL n A) (hg : g ∈ UJ σ J) : bc φ g ∈ UJ σ' (J.map φ) := by
  have hg' : cT σ (g : Matrix n n A) * J * (g : Matrix n n A) = J := hg
  show cT σ' ((bc φ g : GL n B) : Matrix n n B) * J.map φ * ((bc φ g : GL n B) : Matrix n n B) = J.map φ
  rw [bc_coe, incl_cT_map σ σ' φ h, ← Matrix.map_mul, ← Matrix.map_mul, hg']

theorem inclE_injective (F E : Type) [Field F] [CommRing E] [Algebra F E]
    (R : Type) [CommRing R] [Algebra F R] [Nontrivial R] :
    Function.Injective (inclE (F := F) (E := E) R) := by
  intro x y hxy
  exact Algebra.TensorProduct.includeLeft_injective (S := F) (algebraMap F R).injective hxy

theorem UG_inclusion_injective : Formalism.UG.InclInj := by
  intro F E _ _ _ n _ _ R _ _ hR
  haveI := hR
  intro g g' hgg
  apply Units.ext
  have h1 := congrArg Units.val hgg
  rw [bc_coe, bc_coe] at h1
  ext i j
  exact inclE_injective F E R (congrFun (congrFun h1 i) j)

private lemma sigR_tmul_adelic_iwasawa_hecke (F E : Type) [Field F] [CommRing E] [Algebra F E] (σ : E →ₐ[F] E)
    (x : E) (c : F) : Formalism.UG.sigR σ F (x ⊗ₜ[F] c) = σ x ⊗ₜ[F] c := by
  first
  | rfl
  | simp [Formalism.UG.sigR]
  | (unfold Formalism.UG.sigR; simp)

end Formalism.UG.P
