import Mathlib
import Formalism.CMTypeGalois.StatementGroup

open Finset

namespace Formalism.Q3

namespace TypesB

variable {G : Type*} [CommGroup G] [DecidableEq G] {c : G}

lemma cc_mul' (hc : c * c = 1) (g : G) : c * (c * g) = g := by
  rw [← mul_assoc, hc, one_mul]

lemma mem_image_cmul (hc : c * c = 1) (X : Finset G) (g : G) :
    g ∈ X.image (fun x => c * x) ↔ c * g ∈ X := by
  constructor
  · intro h
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 h
    rwa [cc_mul' hc]
  · intro h
    exact Finset.mem_image.2 ⟨c * g, h, cc_mul' hc g⟩

lemma exists_cmType [Fintype G] (hc1 : c ≠ 1) (hc : c * c = 1) :
    ∃ H : Finset G, IsCMTypeG c H ∧ 1 ∈ H := by
  let e := Fintype.equivFin G
  refine ⟨univ.filter (fun g => g = 1 ∨ (g ≠ c ∧ e g < e (c * g))), ?_, by simp⟩
  intro g
  simp only [mem_filter, mem_univ, true_and, cc_mul' hc]
  by_cases h1 : g = 1
  · subst h1
    simp [hc1]
  by_cases h2 : g = c
  · subst h2
    simp [hc, hc1]
  have h3 : c * g ≠ 1 := by
    intro h
    apply h2
    have := congrArg (fun x => c * x) h
    simp only [cc_mul' hc, mul_one] at this
    exact this
  have h4 : c * g ≠ c := by
    intro h
    apply h1
    exact mul_left_cancel (h.trans (mul_one c).symm)
  have h5 : e g ≠ e (c * g) := by
    intro h
    have h' : g = c * g := e.injective h
    apply hc1
    have : 1 * g = c * g := by rw [one_mul]; exact h'
    exact (mul_right_cancel this).symm
  simp only [h1, h2, h3, h4, false_or, ne_eq, not_false_eq_true, true_and, not_lt]
  exact ⟨le_of_lt, fun h => lt_of_le_of_ne h h5⟩

def ext (c : G) (H S : Finset G) : Finset G := S ∪ (H \ S).image (fun x => c * x)

lemma mem_ext (hc : c * c = 1) (H S : Finset G) (x : G) :
    x ∈ ext c H S ↔ x ∈ S ∨ (c * x ∈ H ∧ c * x ∉ S) := by
  unfold ext
  rw [mem_union, mem_image_cmul hc, mem_sdiff]

end TypesB

end Formalism.Q3
