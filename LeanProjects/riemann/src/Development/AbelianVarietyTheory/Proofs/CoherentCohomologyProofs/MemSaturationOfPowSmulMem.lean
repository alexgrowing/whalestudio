import Mathlib

namespace GlobalTheory.SubmoduleSaturation

variable {A : Type*} [CommRing A] {M : Type*} [AddCommGroup M] [Module A M]

def saturation (g : A) (K : Submodule A M) : Submodule A M where
  carrier := {m | ∃ k : ℕ, g ^ k • m ∈ K}
  zero_mem' := ⟨0, by simp⟩
  add_mem' := by
    rintro a b ⟨k, hk⟩ ⟨l, hl⟩
    refine ⟨k + l, ?_⟩
    rw [smul_add]
    refine K.add_mem ?_ ?_
    · rw [add_comm, pow_add, mul_smul]
      exact K.smul_mem _ hk
    · rw [pow_add, mul_smul]
      exact K.smul_mem _ hl
  smul_mem' := by
    rintro c a ⟨k, hk⟩
    refine ⟨k, ?_⟩
    rw [smul_comm]
    exact K.smul_mem _ hk

theorem le_saturation (g : A) (K : Submodule A M) : K ≤ saturation g K :=
  fun m hm => ⟨0, by simpa using hm⟩

end GlobalTheory.SubmoduleSaturation
