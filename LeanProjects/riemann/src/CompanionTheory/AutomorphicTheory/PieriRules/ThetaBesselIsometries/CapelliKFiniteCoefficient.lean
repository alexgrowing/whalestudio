import Mathlib
import CompanionTheory.AutomorphicTheory.PieriRules.PieriDegreeBounds.Imports
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.DiscreteSeriesUnitarySmoothBasic
import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.IsDSOfIsDG

namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory

theorem comp_eq_sum_inner_smul_rankOne {H Wp Wq : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] {ι κ : Type} [Fintype ι] [Fintype κ]
    (b : OrthonormalBasis ι ℂ Wp) (c : OrthonormalBasis κ ℂ Wq)
    (P : H →L[ℂ] Wp) (A : H →L[ℂ] H) (Q : Wq →L[ℂ] H) :
    P.comp (A.comp Q) = ∑ p : ι × κ, ⟪ContinuousLinearMap.adjoint P (b p.1), A (Q (c p.2))⟫_ℂ •
      (innerSL ℂ (c p.2)).smulRight (b p.1) := by
  ext x
  simp only [ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.smulRight_apply,
    innerSL_apply_apply, Fintype.sum_prod_type, smul_smul]
  conv_lhs => rw [← c.sum_repr' x]
  simp only [map_sum, map_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  conv_lhs => rw [← b.sum_repr' (P (A (Q (c j))))]
  simp only [Finset.smul_sum, smul_smul, mul_comm]

theorem isCoef_of_translate_smul_exists : PI.KFinSmooth → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (Wq : Type) [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [CompleteSpace Wq] [FiniteDimensional ℂ Wq] (l : R.H → Wp) (l' : R.H → Wq), R.IsDG ε mu → (∀ f : Mx k r → (Wq →L[ℂ] Wp), PI.CapelliEig.IsKFinCoefT (k := k) (r := r) R.σ f → ∃ s, IsCoef R l l' f s) ∧ (∀ F s (t : ℂ), IsCoef R l l' F s → IsCoef R l l' (fun g => t • F g) (t * s)) ∧ ((∃ x ∈ R.TK, l x ≠ 0) → (∃ y ∈ R.TK, l' y ≠ 0) → ∀ s : ℂ, ∃ F, IsCoef R l l' F s) := by
  intro hK k r ε mu R Wp _ _ _ _ Wq _ _ _ _ l l' hR
  obtain ⟨hmul, hone, hinner, -, -, hTK, hKF, -, -⟩ := rep_basic_of_isDS hK k r ε mu R hR
  refine ⟨?_, ?_, ?_⟩
  · rintro f ⟨a, ha, b, hb, P, Q, hQ, hP, h⟩
    obtain ⟨hai, ha1, -⟩ := Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.uh_inv ha
    obtain ⟨hbi, -, hb2⟩ := Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.uh_inv hb
    let e := stdOrthonormalBasis ℂ Wp
    let c := stdOrthonormalBasis ℂ Wq
    let φ := (finProdFinEquiv (m := Module.finrank ℂ Wp) (n := Module.finrank ℂ Wq)).symm
    refine ⟨_, _, fun i => R.σ a (ContinuousLinearMap.adjoint P (e (φ i).1)),
      fun i => R.σ b⁻¹ (Q (c (φ i).2)), fun i => (innerSL ℂ (c (φ i).2)).smulRight (e (φ i).1),
      fun i => ⟨hTK a ha _ (hKF _ (hP _)), hTK _ hbi _ (hKF _ (hQ _))⟩, fun g hg => ?_, rfl⟩
    have hc : a * (a⁻¹ * g * b⁻¹) * b = g := by
      calc a * (a⁻¹ * g * b⁻¹) * b = (a * a⁻¹) * g * (b⁻¹ * b) := by simp only [Matrix.mul_assoc]
        _ = g := by rw [ha1, hb2, Matrix.one_mul, Matrix.mul_one]
    have h1 : f g = P.comp ((R.σ (a⁻¹ * g * b⁻¹)).comp Q) := by
      have := h (a⁻¹ * g * b⁻¹)
      simpa only [hc] using this
    have hm : a⁻¹ * g * b⁻¹ ∈ GG k r :=
      Formalism.FourierDecayAlt.P.TranslationBesselVanishing.uh_mul (Formalism.FourierDecayAlt.P.TranslationBesselVanishing.uh_mul hai hg) hbi
    have h2 : ∀ u v, ⟪u, R.σ (a⁻¹ * g * b⁻¹) v⟫_ℂ = ⟪R.σ a u, R.σ g (R.σ b⁻¹ v)⟫_ℂ := by
      intro u v
      rw [← hinner a ha, ← hmul a ha _ hm, ← hmul g hg _ hbi, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ha1,
        Matrix.one_mul]
    rw [h1, comp_eq_sum_inner_smul_rankOne e c]
    simp only [h2]
    exact (φ.sum_comp (fun p => ⟪R.σ a (ContinuousLinearMap.adjoint P (e p.1)), R.σ g (R.σ b⁻¹ (Q (c p.2)))⟫_ℂ •
      (innerSL ℂ (c p.2)).smulRight (e p.1))).symm
  · rintro F s t ⟨m, x, y, X, hxy, hF, hs⟩
    refine ⟨m, x, y, fun i => t • X i, hxy, fun g hg => ?_, ?_⟩
    · simp only [hF g hg, Finset.smul_sum, smul_smul, mul_comm]
    · simp only [hs, Finset.mul_sum, ContinuousLinearMap.smul_apply, inner_smul_right]
  · rintro ⟨x, hx, hx0⟩ ⟨y, hy, hy0⟩ s
    have h1 : ⟪l x, l x⟫_ℂ ≠ 0 := fun h => hx0 (inner_self_eq_zero.mp h)
    have h2 : ⟪l' y, l' y⟫_ℂ ≠ 0 := fun h => hy0 (inner_self_eq_zero.mp h)
    refine ⟨fun g => ∑ _i : Fin 1, ⟪x, R.σ g y⟫_ℂ •
        ((s / (⟪l' y, l' y⟫_ℂ * ⟪l x, l x⟫_ℂ)) • (innerSL ℂ (l' y)).smulRight (l x)),
      1, fun _ => x, fun _ => y,
      fun _ => (s / (⟪l' y, l' y⟫_ℂ * ⟪l x, l x⟫_ℂ)) • (innerSL ℂ (l' y)).smulRight (l x),
      fun _ => ⟨hx, hy⟩, fun g _ => rfl, ?_⟩
    rw [Fin.sum_univ_one, ContinuousLinearMap.smul_apply, ContinuousLinearMap.smulRight_apply,
      innerSL_apply_apply, inner_smul_right, inner_smul_right, div_mul_cancel₀ _ (mul_ne_zero h2 h1)]

end GlobalTheory
