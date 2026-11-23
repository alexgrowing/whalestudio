import Mathlib
import ReciprocityTheory.DualLattices.CotangentSurjective
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsTight
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.StepOrderRes

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix

namespace GlobalTheory.CompanionTheory.Ar.GR

private theorem sum_smul_cols_eq_mul_vec {C R X : Type} [Field C] [CommRing R] [Algebra R C]
    [Fintype X] (B : Matrix X X C) (c : X → R) :
    (∑ j, c j • fun x => B x j) = B *ᵥ fun j => algebraMap R C (c j) := by
  funext x
  simp only [Finset.sum_apply, Pi.smul_apply]
  simp only [Matrix.mulVec, dotProduct, Algebra.smul_def, mul_comm]

theorem mem_span_cols_iff {C R X : Type} [Field C] [CommRing R] [Algebra R C] [Fintype X]
    [DecidableEq X] (B : Matrix X X C) (hB : IsUnit B.det) (u : X → C) :
    u ∈ Submodule.span R (Set.range fun j x => B x j) ↔
      ∀ j, ∃ r : R, algebraMap R C r = (B⁻¹ *ᵥ u) j := by
  have hinv : B⁻¹ * B = 1 := Matrix.nonsing_inv_mul B hB
  have hinv' : B * B⁻¹ = 1 := Matrix.mul_nonsing_inv B hB
  rw [Submodule.mem_span_range_iff_exists_fun]
  constructor
  · rintro ⟨c, rfl⟩ j
    refine ⟨c j, ?_⟩
    rw [sum_smul_cols_eq_mul_vec, Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]
  · intro h
    choose c hc using h
    refine ⟨c, ?_⟩
    have e : (fun j => algebraMap R C (c j)) = B⁻¹ *ᵥ u := funext hc
    rw [sum_smul_cols_eq_mul_vec, e, Matrix.mulVec_mulVec, hinv', Matrix.one_mulVec]

theorem exists_denominator {C R X : Type} [Field C] [CommRing R] [Algebra R C]
    (v : Valuation C NNReal) (hv : v.Integers R) [Fintype X] [Nonempty X] (w : X → C) :
    ∃ c : R, c ≠ 0 ∧ ∀ d : R,
      (∀ j, ∃ r : R, algebraMap R C r = algebraMap R C d * w j) ↔ d ∈ Ideal.span {c} := by
  classical
  by_cases hall : ∀ j, v (w j) ≤ 1
  · have h10 : (1 : R) ≠ 0 := by
      intro h
      have h' := congrArg (algebraMap R C) h
      simp at h'
    refine ⟨1, h10, fun d => ?_⟩
    constructor
    · intro _
      simp [Ideal.span_singleton_one]
    · intro _ j
      apply hv.exists_of_le_one
      rw [map_mul]
      calc v (algebraMap R C d) * v (w j) ≤ 1 * 1 := mul_le_mul' (hv.map_le_one d) (hall j)
        _ = 1 := one_mul 1
  · push Not at hall
    obtain ⟨j1, hj1⟩ := hall
    obtain ⟨j0, -, hj0⟩ :=
      Finset.exists_max_image Finset.univ (fun j => v (w j)) Finset.univ_nonempty
    have hgt : 1 < v (w j0) := lt_of_lt_of_le hj1 (hj0 j1 (Finset.mem_univ _))
    have hw0 : w j0 ≠ 0 := by
      intro h
      simp [h] at hgt
    have hinvle : v (w j0)⁻¹ ≤ 1 := by
      rw [map_inv₀]
      exact inv_le_one_of_one_le₀ hgt.le
    obtain ⟨c, hc⟩ := hv.exists_of_le_one hinvle
    have hc0 : c ≠ 0 := by
      rintro rfl
      rw [map_zero] at hc
      exact inv_ne_zero hw0 hc.symm
    refine ⟨c, hc0, fun d => ?_⟩
    rw [Ideal.mem_span_singleton, hv.dvd_iff_le, hc]
    constructor
    · intro h
      obtain ⟨r, hr⟩ := h j0
      have e : algebraMap R C d = (algebraMap R C d * w j0) * (w j0)⁻¹ :=
        (mul_inv_cancel_right₀ hw0 _).symm
      rw [e, map_mul, ← hr]
      exact mul_le_of_le_one_left zero_le (hv.map_le_one r)
    · intro h j
      apply hv.exists_of_le_one
      rw [map_mul]
      calc v (algebraMap R C d) * v (w j) ≤ v (w j0)⁻¹ * v (w j0) :=
            mul_le_mul' h (hj0 j (Finset.mem_univ _))
        _ = 1 := by rw [← map_mul, inv_mul_cancel₀ hw0, map_one]

private theorem smul_algebra_map_char_eq {C R F : Type} [Field C] [CommRing R] [Algebra R C] [Field F]
    (χ : MulChar F R) (c : R) :
    (c • fun a => algebraMap R C (χ a)) = fun a => algebraMap R C (c * χ a) := by
  funext a
  simp only [Pi.smul_apply, Algebra.smul_def, map_mul]

theorem eig_rank_one : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p] (f : ℕ), Fintype.card F = p ^ f → ∀ (AA : HopfOrder (C := C) R F), FStable F AA.carrier → ∀ χ : MulChar F R, (∃ c : R, c ≠ 0 ∧ xIdeal AA.carrier χ = Ideal.span {c}) ∧ ∀ g, g ∈ eig AA.carrier χ ↔ ∃ c ∈ xIdeal AA.carrier χ, g = fun a => algebraMap R C (c * χ a) := by
  intro p _ C _ _ _ v R _ _ hv _ F _ _ _ _ f _ AA _ χ
  obtain ⟨B, hB, hM⟩ := AA.lat
  have key : ∀ d : R, d ∈ xIdeal AA.carrier χ ↔
      (d • fun a => algebraMap R C (χ a)) ∈ AA.carrier := fun d => by
    simp only [xIdeal, Submodule.mem_comap, LinearMap.toSpanSingleton_apply]
  refine ⟨?_, ?_⟩
  · obtain ⟨c, hc0, hc⟩ := exists_denominator v hv (B⁻¹ *ᵥ fun a => algebraMap R C (χ a))
    refine ⟨c, hc0, ?_⟩
    ext d
    rw [key, hM, mem_span_cols_iff B hB, ← hc d]
    refine forall_congr' fun j => exists_congr fun r => ?_
    rw [Matrix.mulVec_smul, Pi.smul_apply, Algebra.smul_def]
  · intro g
    constructor
    · rintro ⟨hgM, hg⟩
      have hint : ∀ x, ∃ r : R, algebraMap R C r = g x := AA.le_int hgM
      obtain ⟨r, hr⟩ := hint 1
      have hgf : g = fun a => algebraMap R C (r * χ a) := by
        funext a
        have h := hg a 1
        rw [smul_eq_mul, mul_one] at h
        rw [h, ← hr, map_mul]
        exact mul_comm _ _
      refine ⟨r, ?_, hgf⟩
      rw [key, smul_algebra_map_char_eq, ← hgf]
      exact hgM
    · rintro ⟨c, hc, rfl⟩
      rw [key, smul_algebra_map_char_eq] at hc
      refine ⟨hc, fun a x => ?_⟩
      simp only [smul_eq_mul, map_mul]
      ring

end GlobalTheory.CompanionTheory.Ar.GR
