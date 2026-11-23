import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut

open MeasureTheory Formalism.MainNotions.S
open scoped InnerProductSpace ComplexOrder

namespace GlobalTheory.CharIdem

section

variable {G : Type} [Group G]

open Classical in

noncomputable def charFn (K : Subgroup G) (χ : K →* Circle) (c : ℝ) : G → ℂ :=
  fun x => if h : x ∈ K then star ((χ ⟨x, h⟩ : Circle) : ℂ) / (c : ℂ) else 0

variable (K : Subgroup G) (χ : K →* Circle) (c : ℝ)

theorem sum_fiber_nonneg {ι Q : Type} [Fintype ι] [DecidableEq Q] (q : ι → Q) (a : ι → ℂ) :
    0 ≤ ∑ i, ∑ j, (if q i = q j then star (a i) * a j else 0) := by
  have h : ∑ i, ∑ j, (if q i = q j then star (a i) * a j else 0) =
      ∑ t ∈ Finset.univ.image q, star (∑ i, if q i = t then a i else 0) *
        (∑ j, if q j = t then a j else 0) := by
    simp only [star_sum, Finset.sum_mul_sum]
    rw [Finset.sum_comm]
    symm
    rw [Finset.sum_comm]
    rw [Finset.sum_comm (s := Finset.univ) (t := Finset.univ)
      (f := fun j i => if q i = q j then star (a i) * a j else 0)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_eq_single (q i)]
    · by_cases hij : q i = q j
      · simp [hij]
      · simp [hij, Ne.symm hij]
    · intro b _ hb
      simp [Ne.symm hb]
    · intro hb
      exact absurd (Finset.mem_image_of_mem q (Finset.mem_univ i)) hb
  rw [h]
  exact Finset.sum_nonneg fun t _ => star_mul_self_nonneg _

variable [TopologicalSpace G] [IsTopologicalGroup G]

variable [MeasurableSpace G] [BorelSpace G]

end

end GlobalTheory.CharIdem
