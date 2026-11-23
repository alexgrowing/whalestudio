import Mathlib

open Finset

noncomputable section

namespace PI.RamBoundW

section Fil

variable {R P : Type*} [CommRing R] [CommRing P] [Algebra R P] {ι : Type*} (δ : ι → Derivation R P P)

def apL : List ι → P →ₗ[R] P
  | [] => LinearMap.id
  | i :: T => apL T ∘ₗ (δ i).toLinearMap

@[simp] theorem apL_nil (M : P) : apL δ [] M = M := rfl

@[simp] theorem apL_cons (i : ι) (T : List ι) (M : P) : apL δ (i :: T) M = apL δ T (δ i M) := rfl

def Fil (a : ℕ) : Submodule R P where
  carrier := {M | ∀ T : List ι, a < T.length → apL δ T M = 0}
  add_mem' := by
    intro M N hM hN T hT
    rw [map_add, hM T hT, hN T hT, add_zero]
  zero_mem' := by
    intro T _
    exact map_zero _
  smul_mem' := by
    intro r M hM T hT
    rw [map_smul, hM T hT, smul_zero]

variable {δ}

end Fil

section Leib

variable {R P : Type*} [CommRing R] [CommRing P] [Algebra R P]

end Leib

end PI.RamBoundW
