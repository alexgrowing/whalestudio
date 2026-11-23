import Mathlib
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.InvariantSubspaceMobiusInverseRecEqOfFinrankLt

open Polynomial GlobalTheory.CuspGL

namespace GlobalTheory.CuspGL

variable {F : Type} [Field F]

theorem finite_monic_factorisations (P : F[X]) :
    {x : F[X] × F[X] | x.1.Monic ∧ x.2.Monic ∧ x.1 * x.2 = P}.Finite := by
  by_cases hP : P = 0
  · convert Set.finite_empty
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨h1, h2, h3⟩
    exact (h1.mul h2).ne_zero (h3.trans hP)
  · have hfin : {D : F[X] | D.Monic ∧ D ∣ P}.Finite := by
      letI : Fintype {D : F[X] | D.Monic ∧ D ∣ P} := Polynomial.fintypeSubtypeMonicDvd P hP
      exact Set.toFinite _
    refine (hfin.prod hfin).subset ?_
    rintro x ⟨h1, h2, h3⟩
    exact ⟨⟨h1, h3 ▸ dvd_mul_right _ _⟩, ⟨h2, h3 ▸ dvd_mul_left _ _⟩⟩

theorem conv_eq_sum (a b : F[X] → ℂ) (P : F[X]) :
    conv a b P = ∑ x ∈ (finite_monic_factorisations P).toFinset, a x.1 * b x.2 :=
  finsum_mem_eq_finite_toFinset_sum _ (finite_monic_factorisations P)

theorem conv_comm (a b : F[X] → ℂ) (P : F[X]) : conv a b P = conv b a P := by
  rw [conv_eq_sum, conv_eq_sum]
  refine Finset.sum_nbij' Prod.swap Prod.swap ?_ ?_ ?_ ?_ ?_
  · intro x hx
    simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hx ⊢
    exact ⟨hx.2.1, hx.1, by rw [← hx.2.2]; exact mul_comm _ _⟩
  · intro x hx
    simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hx ⊢
    exact ⟨hx.2.1, hx.1, by rw [← hx.2.2]; exact mul_comm _ _⟩
  · intro x _; rfl
  · intro x _; rfl
  · intro x _; exact mul_comm _ _

theorem conv_assoc (a b c : F[X] → ℂ) (P : F[X]) :
    conv (conv a b) c P = conv a (conv b c) P := by
  rw [conv_eq_sum, conv_eq_sum]
  simp only [conv_eq_sum, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_sigma', Finset.sum_sigma']
  refine Finset.sum_nbij' (fun z => ⟨(z.2.1, z.2.2 * z.1.2), (z.2.2, z.1.2)⟩)
    (fun z => ⟨(z.1.1 * z.2.1, z.2.2), (z.1.1, z.2.1)⟩) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨⟨D, E⟩, ⟨A, B⟩⟩ hx
    simp only [Finset.mem_sigma, Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hx ⊢
    obtain ⟨⟨h1, h2, h3⟩, h4, h5, h6⟩ := hx
    exact ⟨⟨h4, h5.mul h2, by rw [← mul_assoc, h6, h3]⟩, h5, h2, trivial⟩
  · rintro ⟨⟨D, E⟩, ⟨A, B⟩⟩ hx
    simp only [Finset.mem_sigma, Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hx ⊢
    obtain ⟨⟨h1, h2, h3⟩, h4, h5, h6⟩ := hx
    exact ⟨⟨h1.mul h4, h5, by rw [mul_assoc, h6, h3]⟩, h1, h4, trivial⟩
  · rintro ⟨⟨D, E⟩, ⟨A, B⟩⟩ hx
    simp only [Finset.mem_sigma, Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hx
    obtain ⟨⟨h1, h2, h3⟩, h4, h5, h6⟩ := hx
    subst h6
    rfl
  · rintro ⟨⟨D, E⟩, ⟨A, B⟩⟩ hx
    simp only [Finset.mem_sigma, Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hx
    obtain ⟨⟨h1, h2, h3⟩, h4, h5, h6⟩ := hx
    subst h6
    rfl
  · rintro ⟨⟨D, E⟩, ⟨A, B⟩⟩ _
    exact mul_assoc _ _ _

theorem conv_add_left (a b c : F[X] → ℂ) (P : F[X]) :
    conv (a + b) c P = conv a c P + conv b c P := by
  simp only [conv_eq_sum, Pi.add_apply, add_mul, Finset.sum_add_distrib]

theorem conv_sub_left (a b c : F[X] → ℂ) (P : F[X]) :
    conv (a - b) c P = conv a c P - conv b c P := by
  simp only [conv_eq_sum, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

theorem conv_basic : ∀ (F : Type) [Field F] (P : F[X]), P.Monic → {x : F[X] × F[X] | x.1.Monic ∧ x.2.Monic ∧ x.1 * x.2 = P}.Finite ∧ ∀ a b c : F[X] → ℂ, conv a b P = conv b a P ∧ conv (conv a b) c P = conv a (conv b c) P ∧ conv (a + b) c P = conv a c P + conv b c P ∧ conv (a - b) c P = conv a c P - conv b c P :=
  fun _ _ P _ => ⟨finite_monic_factorisations P, fun a b c =>
    ⟨conv_comm a b P, conv_assoc a b c P, conv_add_left a b c P, conv_sub_left a b c P⟩⟩

end GlobalTheory.CuspGL
