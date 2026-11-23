import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL

noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.ParabLevel

open GlobalTheory.SmGL

section General

variable {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R]
  {n : Type} [Fintype n] [DecidableEq n]

theorem isClosed_parab_two {a b : Type} (e : a ⊕ b ≃ n) :
    IsClosed (parab R (two e) : Set (GL n R)) := by
  have h : (parab R (two e) : Set (GL n R)) =
      ⋂ (j : b) (i : a), {g : GL n R | (g : Matrix n n R) (e (.inr j)) (e (.inl i)) = 0} := by
    ext g
    simp only [SetLike.mem_coe, Set.mem_iInter, Set.mem_setOf_eq]
    exact mem_parab_two R
  rw [h]
  exact isClosed_iInter fun j => isClosed_iInter fun i =>
    isClosed_eq (Units.continuous_val.matrix_elem _ _) continuous_const

theorem continuous_leviProj {α : Type} {m : α → Type} [Fintype α] [LinearOrder α] [∀ x, Fintype (m x)]
    [∀ x, DecidableEq (m x)] (e : (Σ x, m x) ≃ n) : Continuous (leviProj R e) := by
  refine continuous_pi fun x => Units.continuous_iff.2 ⟨?_, ?_⟩
  · refine continuous_matrix fun i j => ?_
    show Continuous fun p : parab R e => ((p : GL n R) : Matrix n n R) (e ⟨x, i⟩) (e ⟨x, j⟩)
    exact (Units.continuous_val.comp continuous_subtype_val).matrix_elem _ _
  · have hc : Continuous fun p : parab R e => ((leviProj R e p⁻¹ x : GL (m x) R) : Matrix (m x) (m x) R) := by
      refine continuous_matrix fun i j => ?_
      show Continuous fun p : parab R e => (((p⁻¹ : parab R e) : GL n R) : Matrix n n R) (e ⟨x, i⟩) (e ⟨x, j⟩)
      exact ((Units.continuous_val.comp continuous_subtype_val).comp continuous_inv).matrix_elem _ _
    refine hc.congr fun p => ?_
    rw [map_inv]
    rfl

theorem continuous_leviTwo_symm {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] :
    Continuous (leviTwo R a b).symm :=
  (continuous_apply false).prodMk (continuous_apply true)

end General

end GlobalTheory.ParabLevel
