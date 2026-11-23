import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DlogRatioVolumeFormNeZero

open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

set_option autoImplicit false

namespace GlobalTheory.MonoCech

variable {ι : Type} [LinearOrder ι] {E : Type} [AddCommGroup E]

def cone (i : ι) (c : Finset ι → E) : Finset ι → E := fun t =>
  if i ∈ t then 0 else cubeSign (insert i t) i • c (insert i t)

theorem delta_cone_add (i : ι) (c : Finset ι → E) :
    GlobalTheory.DI.delta (cone i c) + cone i (GlobalTheory.DI.delta c) = c := by
  funext t
  simp only [Pi.add_apply, GlobalTheory.DI.delta, cone]
  by_cases hi : i ∈ t
  · rw [if_pos hi, add_zero, Finset.sum_eq_single i]
    · rw [if_neg (by simp), Finset.insert_erase hi, smul_smul, cubeSign_mul_self, one_smul]
    · intro j _ hji
      rw [if_pos (Finset.mem_erase.2 ⟨Ne.symm hji, hi⟩), smul_zero]
    · intro h; exact absurd hi h
  · rw [if_neg hi, Finset.sum_insert hi, Finset.erase_insert hi, smul_add, smul_smul, cubeSign_mul_self,
      one_smul, Finset.smul_sum]
    have key : ∀ j ∈ t, cubeSign t j • (if i ∈ t.erase j then (0 : E) else
        cubeSign (insert i (t.erase j)) i • c (insert i (t.erase j))) +
        cubeSign (insert i t) i • cubeSign (insert i t) j • c ((insert i t).erase j) = 0 := by
      intro j hj
      have hij : i ≠ j := fun h => hi (h ▸ hj)
      rw [if_neg (fun h => hi (Finset.mem_of_mem_erase h)), ← Finset.erase_insert_of_ne hij, smul_smul,
        smul_smul, ← add_smul]
      have h1 := cubeSign_mul_erase (t := insert i t) (i := i) (j := j) (Finset.mem_insert_self _ _)
        (Finset.mem_insert_of_mem hj) hij
      rw [Finset.erase_insert hi] at h1
      have ha := cubeSign_mul_self (insert i t) i
      have he := cubeSign_mul_self ((insert i t).erase j) i
      have : cubeSign t j * cubeSign ((insert i t).erase j) i + cubeSign (insert i t) i * cubeSign (insert i t) j = 0 := by
        linear_combination (cubeSign (insert i t) i * cubeSign ((insert i t).erase j) i) * h1
          - (cubeSign t j * cubeSign ((insert i t).erase j) i) * ha
          - (cubeSign (insert i t) i * cubeSign (insert i t) j) * he
      rw [this, zero_smul]
    rw [add_left_comm, ← Finset.sum_add_distrib, Finset.sum_eq_zero key, add_zero]

theorem cone_zero (i : ι) : cone i (0 : Finset ι → E) = 0 := by
  funext t; simp [cone]

end GlobalTheory.MonoCech

namespace GlobalTheory.MonoCech

end GlobalTheory.MonoCech
