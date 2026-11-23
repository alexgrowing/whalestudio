import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralGauTwistedConv
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IntegrableMonomialMulConjComplexGaussian

open MeasureTheory Complex
open scoped InnerProductSpace Real

namespace GlobalTheory.RealWeil

section Abstract

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V]
  [BorelSpace V] {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {J : V ≃ₗᵢ[ℝ] V}
  {ρ : V → H →L[ℂ] H}

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] [CompleteSpace H] in

theorem IsHeis.inner_left (hJ : ∀ x, J (J x) = -x) (h : IsHeis (omJ J) ρ) (u : V) (x y : H) :
    ⟪ρ u x, y⟫_ℂ = ⟪x, ρ (-u) y⟫_ℂ := by
  have h0 : omJ J u (-u) = 0 := by
    have := omJ_skew hJ u u
    have e : omJ J u (-u) = -omJ J u u := by simp [omJ]
    linarith
  have e : ρ u (ρ (-u) y) = y := by
    rw [h.2.1, h0, add_neg_cancel, h.1]
    simp
  have := (⟨(ρ u : H →ₗ[ℂ] H), h.2.2.1 u⟩ : H →ₗᵢ[ℂ] H).inner_map_map x (ρ (-u) y)
  rw [← this]
  change _ = ⟪ρ u x, ρ u (ρ (-u) y)⟫_ℂ
  rw [e]

theorem inner_proj_right {om : V → V → ℝ} (h : IsHeis om ρ) (x y : H) :
    ⟪x, proj h y⟫_ℂ = ∫ u, gau u * ⟪x, ρ u y⟫_ℂ := by
  rw [proj_apply, ← integral_inner (h.integrable y)]
  simp only [inner_smul_right]

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
theorem conj_gau (u : V) : (starRingEnd ℂ) (gau u) = gau u := by
  unfold gau
  rw [← Complex.exp_conj]
  simp [map_ofNat]

theorem inner_proj_left (hJ : ∀ x, J (J x) = -x) (h : IsHeis (omJ J) ρ) (x y : H) :
    ⟪proj h x, y⟫_ℂ = ⟪x, proj h y⟫_ℂ := by
  rw [← inner_conj_symm, inner_proj_right, inner_proj_right, ← integral_conj,
    ← integral_neg_eq_self (fun u => gau u * ⟪x, ρ u y⟫_ℂ)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  simp only [map_mul, conj_gau, inner_conj_symm, gau_neg, h.inner_left hJ]

theorem integral_gau_mul_gau : ∫ u : V, gau u * gau u = 1 := by
  have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have key := GaussianFourier.integral_cexp_neg_mul_sq_norm (V := V) (b := (π : ℂ))
    (by simpa using Real.pi_pos)
  rw [div_self hpi, one_cpow] at key
  rw [← key]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  simp only [gau, ← Complex.exp_add]
  congr 1
  ring

theorem proj_idem (hJ : ∀ x, J (J x) = -x) (h : IsHeis (omJ J) ρ) (x : H) :
    proj h (proj h x) = proj h x := by
  have := proj_heis_proj hJ h 0 x
  rwa [h.1, gau_zero, one_smul] at this

theorem proj_eq_self_of_vacuum (hJ : ∀ x, J (J x) = -x) (h : IsHeis (omJ J) ρ) {v : H}
    (hv : ∀ a, ⟪v, ρ a v⟫_ℂ = gau a * ⟪v, v⟫_ℂ) : proj h v = v := by
  have h1 : ⟪v, proj h v⟫_ℂ = ⟪v, v⟫_ℂ := by
    rw [inner_proj_right]
    simp only [hv, ← mul_assoc]
    rw [integral_mul_const, integral_gau_mul_gau, one_mul]
  rw [← sub_eq_zero, ← inner_self_eq_zero (𝕜 := ℂ), inner_sub_left, inner_sub_right, inner_sub_right,
    inner_proj_left hJ, inner_proj_left hJ, proj_idem hJ, h1]
  ring

theorem eq_zero_of_orthogonal_translates_proj (hJ : ∀ x, J (J x) = -x) (h : IsHeis (omJ J) ρ) {x : H}
    (hx : ∀ y a, ⟪ρ a (proj h y), x⟫_ℂ = 0) : x = 0 := by
  have h1 : ∀ a, proj h (ρ (-a) x) = 0 := fun a => by
    refine ext_inner_left ℂ fun y => ?_
    rw [← inner_proj_left hJ, ← h.inner_left hJ, hx, inner_zero_right]
  have hg : Good h x := fun n => by simp [h1]
  rw [← hg.inversion hJ]
  simp [h1]

end Abstract

noncomputable def signUnit (p q : ℕ) : Fin p ⊕ Fin q → Circle :=
  Sum.elim (fun _ => ⟨I, by simp [Submonoid.unitSphere]⟩) (fun _ => ⟨-I, by simp [Submonoid.unitSphere]⟩)

noncomputable def signJ (p q : ℕ) : EuclideanSpace ℂ (Fin p ⊕ Fin q) ≃ₗᵢ[ℝ] EuclideanSpace ℂ (Fin p ⊕ Fin q) :=
  LinearIsometryEquiv.piLpCongrRight 2 fun a => rotation (signUnit p q a)

theorem gau_toLp {ι : Type} [Fintype ι] (z : EuclideanSpace ℂ ι) :
    gau z = Complex.exp (-(Real.pi / 2) * ∑ a, ((‖z a‖ ^ 2 : ℝ) : ℂ)) := by
  rw [gau, ← ofReal_sum, ← EuclideanSpace.norm_sq_eq]
  push_cast
  rfl

end GlobalTheory.RealWeil
