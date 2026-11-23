import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms

namespace GlobalTheory.KFiniteVectors

open Formalism.MainNotions.S

variable {n : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def kFiniteVectors (ε : Fin n → Bool) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) : Submodule ℂ H where
  carrier := {v | IsKFin ε σ v}
  zero_mem' := by
    refine ⟨⊥, inferInstance, Submodule.zero_mem _, ?_⟩
    intro g _ x hx
    rw [Submodule.mem_bot] at hx ⊢
    rw [hx, map_zero]
  add_mem' := by
    rintro a b ⟨S, hS, ha, hSK⟩ ⟨T, hT, hb, hTK⟩
    refine ⟨S ⊔ T, inferInstance, Submodule.add_mem_sup ha hb, ?_⟩
    intro g hg x hx
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
    rw [map_add]
    exact Submodule.add_mem_sup (hSK g hg y hy) (hTK g hg z hz)
  smul_mem' := by
    rintro c a ⟨S, hS, ha, hSK⟩
    exact ⟨S, hS, S.smul_mem c ha, hSK⟩

theorem mem_kFiniteVectors (ε : Fin n → Bool) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (v : H) :
    v ∈ kFiniteVectors ε σ ↔ IsKFin ε σ v := by
  exact Iff.rfl

end GlobalTheory.KFiniteVectors
