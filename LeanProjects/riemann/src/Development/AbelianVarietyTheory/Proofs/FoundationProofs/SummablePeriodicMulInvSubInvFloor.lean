import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.PetIPSmulRight
import Development.AbelianVarietyTheory.Definitions.Foundations.RepL
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory

theorem norm_inv_add_int_sub_inv_add_int_le (z : ℂ) (L : ℝ) (d m : ℤ)
    (hm : |(m : ℝ) - d| ≤ L) (hd : 2 * (‖z‖ + L) + 1 ≤ |(d : ℝ)|) :
    ‖(z + d)⁻¹ - (z + m)⁻¹‖ ≤ 4 * L * (1 / (d : ℝ) ^ 2) := by
  have hL : 0 ≤ L := (abs_nonneg _).trans hm
  have hz : 0 ≤ ‖z‖ := norm_nonneg z
  have key : ∀ x : ℤ, |(x : ℝ)| - ‖z‖ ≤ ‖z + x‖ := by
    intro x
    have h1 : ‖(x : ℂ)‖ ≤ ‖z + x‖ + ‖z‖ := by
      have := norm_sub_le (z + x) z
      simpa using this
    have h2 : ‖(x : ℂ)‖ = |(x : ℝ)| := Complex.norm_intCast x
    linarith
  have hdm : |(d : ℝ)| - L ≤ |(m : ℝ)| := by
    have := abs_sub_abs_le_abs_sub (d : ℝ) m
    rw [abs_sub_comm] at this
    linarith
  have hD : 0 < |(d : ℝ)| / 2 := by linarith
  have h1 : |(d : ℝ)| / 2 ≤ ‖z + d‖ := by have := key d; linarith
  have h2 : |(d : ℝ)| / 2 ≤ ‖z + m‖ := by have := key m; linarith
  have n1 : z + d ≠ 0 := norm_pos_iff.1 (hD.trans_le h1)
  have n2 : z + m ≠ 0 := norm_pos_iff.1 (hD.trans_le h2)
  have e : (z + d)⁻¹ - (z + m)⁻¹ = ((m - d : ℤ) : ℂ) / ((z + d) * (z + m)) := by
    push_cast
    field_simp
    ring
  rw [e, norm_div, norm_mul, Complex.norm_intCast]
  push_cast
  calc |(m : ℝ) - d| / (‖z + d‖ * ‖z + m‖)
      ≤ L / (|(d : ℝ)| / 2 * (|(d : ℝ)| / 2)) := by
        gcongr
    _ = 4 * L * (1 / (d : ℝ) ^ 2) := by
        have : |(d : ℝ)| ≠ 0 := (by linarith : 0 < |(d : ℝ)|).ne'
        rw [← sq_abs (d : ℝ)]
        field_simp
        ring

theorem summable_periodic_mul_inv_sub_inv_floor :
    ∀ (L : ℕ) (φ : ZMod L → ℂ) (z : ℂ), 0 < L → 0 < z.im →
      Summable (fun d : ℤ => φ d * ((z + d)⁻¹ - (z + (L * (d / L) : ℤ))⁻¹)) := by
  intro L φ z hL _
  haveI : NeZero L := ⟨hL.ne'⟩
  set M : ℝ := ∑ y, ‖φ y‖ with hM
  have hφ : ∀ y, ‖φ y‖ ≤ M := fun y =>
    Finset.single_le_sum (f := fun y => ‖φ y‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ y)
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hφ 0)
  have hs : Summable (fun d : ℤ => M * (4 * (L : ℝ) * (1 / (d : ℝ) ^ 2))) :=
    ((Real.summable_one_div_int_pow.2 one_lt_two).mul_left _).mul_left _
  refine Summable.of_norm_bounded_eventually hs ?_
  obtain ⟨N, hN⟩ := exists_nat_ge (2 * (‖z‖ + L) + 1)
  have hfin : (Set.Icc (-(N : ℤ)) N).Finite := Set.finite_Icc _ _
  refine Filter.mem_of_superset hfin.compl_mem_cofinite ?_
  intro d hd
  have hd' : (N : ℤ) ≤ |d| := by
    simp only [Set.mem_compl_iff, Set.mem_Icc, not_and_or, not_le] at hd
    rcases hd with h | h
    · exact le_abs.2 (Or.inr (by omega))
    · exact le_abs.2 (Or.inl h.le)
  have hd'' : (N : ℝ) ≤ |(d : ℝ)| := by exact_mod_cast hd'
  have hL' : (0 : ℤ) < L := by exact_mod_cast hL
  have hm : |(L : ℤ) * (d / L) - d| ≤ L := by
    have a := Int.emod_nonneg d hL'.ne'
    have b := Int.emod_lt_of_pos d hL'
    have c := Int.emod_def d L
    rw [abs_le]
    constructor <;> linarith
  have hm' : |(((L : ℤ) * (d / L) : ℤ) : ℝ) - d| ≤ (L : ℝ) := by exact_mod_cast hm
  have := norm_inv_add_int_sub_inv_add_int_le z L d _ hm' (hN.trans hd'')
  show ‖_‖ ≤ _
  rw [norm_mul]
  exact mul_le_mul (hφ _) this (norm_nonneg _) hM0

end GlobalTheory
