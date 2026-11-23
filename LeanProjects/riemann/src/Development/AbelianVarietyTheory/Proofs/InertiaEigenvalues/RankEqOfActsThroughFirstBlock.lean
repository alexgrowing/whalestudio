import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ResidualConstruction
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSpanRingCornerIdealModuleIff
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices GlobalTheory.SpanRing

namespace GlobalTheory

theorem _root_.GlobalTheory.rank_eq_of_acts_through_first_block {K : Type} [Field K] {n r t : ℕ}
    (e : (Fin n → K) ≃ₗ[K] ((Fin r → K) × (Fin t → K))) (F : Matrix (Fin n) (Fin n) K)
    (ε : Matrix (Fin r) (Fin r) K) (h : ∀ u, e (F.mulVec u) = (ε.mulVec (e u).1, 0)) :
    F.rank = ε.rank := by
  have key : (LinearMap.range F.mulVecLin).map (e : (Fin n → K) →ₗ[K] _) =
      (LinearMap.range ε.mulVecLin).map (LinearMap.inl K (Fin r → K) (Fin t → K)) := by
    ext ⟨a, b⟩
    simp only [Submodule.mem_map, LinearMap.mem_range, Matrix.mulVecLin_apply]
    constructor
    · rintro ⟨_, ⟨u, rfl⟩, hx⟩
      rw [LinearEquiv.coe_coe, h] at hx
      exact ⟨_, ⟨(e u).1, rfl⟩, by simpa using hx⟩
    · rintro ⟨_, ⟨v, rfl⟩, hx⟩
      refine ⟨_, ⟨e.symm (v, 0), rfl⟩, ?_⟩
      rw [LinearEquiv.coe_coe, h]
      simpa using hx
  unfold Matrix.rank
  rw [← LinearEquiv.finrank_map_eq e, key]
  exact (Submodule.equivMapOfInjective _ LinearMap.inl_injective _).finrank_eq.symm

end GlobalTheory
