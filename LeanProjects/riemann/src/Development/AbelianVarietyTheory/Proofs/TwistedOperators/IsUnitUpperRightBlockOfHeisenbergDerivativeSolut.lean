import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairInfApply
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockFormApply
open MeasureTheory

noncomputable section

namespace GlobalTheory.FockFamily

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

theorem isUnit_of_injective_clm (B : V →L[ℝ] V) (h : Function.Injective B) : IsUnit B := by
  have hs : Function.Surjective (B : V →ₗ[ℝ] V) := LinearMap.injective_iff_surjective.mp h
  let e : V ≃ₗ[ℝ] V := LinearEquiv.ofBijective (B : V →ₗ[ℝ] V) ⟨h, hs⟩
  let e' : V ≃L[ℝ] V := e.toContinuousLinearEquiv
  refine ⟨(ContinuousLinearEquiv.unitsEquiv ℝ V).symm e', ?_⟩
  ext x; rfl

theorem dense_pair_ne_zero (β : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (q x₀ : V) (hx : β x₀ q ≠ 0) :
    Dense {x | β x q ≠ 0} := by
  have hint : interior ((LinearMap.ker (β.flip q) : Submodule ℝ V) : Set V) = ∅ := by
    by_contra hne
    have := Submodule.eq_top_of_nonempty_interior' _ (Set.nonempty_iff_ne_empty.mpr hne)
    apply hx
    have : x₀ ∈ LinearMap.ker (β.flip q) := by rw [this]; trivial
    simpa using this
  have := interior_eq_empty_iff_dense_compl.mp hint
  convert this using 1
  ext x; simp

theorem isUnit_blockB_of_solution (β : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (hβ : ∀ q, (∀ x, β x q = 0) → q = 0)
    (J : (V × V) →ₗ[ℝ] (V × V)) (g : V → ℂ) (hg : Continuous g) (hg0 : g ≠ 0)
    (hJ : ∀ w x, GlobalTheory.GaussLine.dHeis β (J w) g x = Complex.I * GlobalTheory.GaussLine.dHeis β w g x) :
    IsUnit (blockB J) := by
  apply isUnit_of_injective_clm
  refine (injective_iff_map_eq_zero (blockB J)).mpr ?_
  intro q hq
  apply hβ q
  by_contra hne
  push_neg at hne
  obtain ⟨x₀, hx₀⟩ := hne
  have hzero : ∀ x, β x q ≠ 0 → g x = 0 := by
    intro x hx
    have h := hJ (0, q) x
    have h1 : (J (0, q)).1 = 0 := by rw [← blockB_apply]; exact hq
    simp only [GlobalTheory.GaussLine.dHeis, h1, map_zero] at h
    have key : (((β x q : ℝ) : ℂ) + Complex.I * ((β x (J (0, q)).2 : ℝ) : ℂ)) * g x = 0 := by
      have hpi : (2 * Real.pi : ℂ) ≠ 0 := by
        have := Real.pi_pos; exact_mod_cast (by positivity : (2 * Real.pi : ℝ) ≠ 0)
      have h2 : (2 * Real.pi : ℂ) * ((((β x q : ℝ) : ℂ) + Complex.I * ((β x (J (0, q)).2 : ℝ) : ℂ)) * g x) = 0 := by
        linear_combination (-1 : ℂ) * h + (2 * Real.pi * ((β x q : ℝ) : ℂ) * g x) * Complex.I_sq
      exact (mul_eq_zero.mp h2).resolve_left hpi
    rcases mul_eq_zero.mp key with h3 | h3
    · exfalso; apply hx
      have := congrArg Complex.re h3
      simpa using this
    · exact h3
  apply hg0
  have hd := dense_pair_ne_zero β q x₀ hx₀
  exact Continuous.ext_on hd hg continuous_const (fun x hx => hzero x hx)
