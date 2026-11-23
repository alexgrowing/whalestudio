import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.FamilyStatementOfAbsAndVandermonde
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.ProductLValuesPolynomialBound
import Formalism.SharpRestriction.CuspSpanNormBounds.OnePlaceEstimates

noncomputable section

namespace Formalism.MainNotions.BridgeLemma₂

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.MainNotions.S.Cnt Formalism.MainNotions.BridgeLemma MeasureTheory
open scoped InnerProductSpace ENNReal Matrix

section Gen

variable {n : ℕ} {ε : Fin n → Bool}

theorem deg_fdegOf {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (μ : Measure (Formalism.REAL.UJ ε)) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (d : ℝ) (w : H)
    (h : IsFdeg μ σ d) (hw : w ≠ 0) : fdegOf μ σ w = d := by
  obtain ⟨hd, hall⟩ := h
  have hint := (hall w w w w).2
  have e1 : ∀ g : Formalism.REAL.UJ ε, coefOn σ w w g * star (coefOn σ w w g) =
      (((‖coefOn σ w w g‖ ^ 2 : ℝ)) : ℂ) := by
    intro g
    rw [Complex.star_def, RCLike.mul_conj]
    push_cast
    rfl
  simp only [e1] at hint
  rw [integral_complex_ofReal, inner_self_eq_norm_sq_to_K] at hint
  have key : (∫ g, ‖coefOn σ w w g‖ ^ 2 ∂μ : ℝ) = ‖w‖ ^ 4 / d := by
    have h3 : ((‖w‖ : ℂ) ^ 2 * (‖w‖ : ℂ) ^ 2 / (d : ℂ)) = ((‖w‖ ^ 4 / d : ℝ) : ℂ) := by
      push_cast
      ring
    have h2 : ((∫ g, ‖coefOn σ w w g‖ ^ 2 ∂μ : ℝ) : ℂ) = ((‖w‖ ^ 4 / d : ℝ) : ℂ) := hint.trans h3
    exact_mod_cast h2
  have hn : ‖w‖ ≠ 0 := norm_ne_zero_iff.2 hw
  unfold fdegOf
  rw [key]
  field_simp

theorem deg_fdegOf_equiv {H H' : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup H']
    [InnerProductSpace ℂ H'] (m : Measure (Formalism.REAL.UJ ε)) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H))
    (σ' : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H')) (U : H ≃ₗᵢ[ℂ] H')
    (hU : ∀ g ∈ UJset ε, ∀ x, U (σ g x) = σ' g (U x)) (v : H) : fdegOf m σ v = fdegOf m σ' (U v) := by
  have hi : ∀ g : Formalism.REAL.UJ ε, coefOn σ' (U v) (U v) g = coefOn σ v v g := by
    intro g
    unfold coefOn
    rw [← hU (umat g) (by exact g.2) v, U.inner_map_map]
  unfold fdegOf
  simp only [hi, U.norm_map]

theorem deg_fdegOf_smul {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (c : NNReal) (hc : 0 < c)
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (v : H) :
    fdegOf (Formalism.REAL.muG ε) σ v = (c : ℝ) * fdegOf (((c : NNReal) : ℝ≥0∞) • Formalism.REAL.muG ε) σ v := by
  unfold fdegOf
  rw [integral_smul_measure, ENNReal.coe_toReal, smul_eq_mul]
  have hc' : (c : ℝ) ≠ 0 := by exact_mod_cast hc.ne'
  rw [← mul_div_assoc, mul_div_mul_left _ _ hc']

theorem deg_inner_isom {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (T : H →L[ℂ] H)
    (hT : ∀ v, ‖T v‖ = ‖v‖) (x y : H) : ⟪T x, T y⟫_ℂ = ⟪x, y⟫_ℂ :=
  let T' : H →ₗᵢ[ℂ] H := { toLinearMap := T.toLinearMap, norm_map' := hT }
  T'.inner_map_map x y

theorem deg_UJ_mul {a b : Matrix (Fin n) (Fin n) ℂ} (ha : a ∈ UJset ε) (hb : b ∈ UJset ε) : a * b ∈ UJset ε := by
  simp only [UJset, Set.mem_setOf_eq] at *
  unfold Formalism.REAL.inUJ at *
  rw [Matrix.conjTranspose_mul]
  simp only [Matrix.mul_assoc] at *
  rw [← Matrix.mul_assoc _ a b, ← Matrix.mul_assoc aᴴ _ b, ha]
  exact hb

end Gen

theorem deg_isFdeg_cayley {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (m : Measure (Formalism.REAL.UJ ε))
    (σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H))
    (P P' : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (hP : IsCayley k r ε P) (hP' : IsCayley k r ε P')
    (hrep : IsURepOn (UJset ε) (fun g => σ (P'⁻¹ * g * P'))) (d : ℝ)
    (hd : IsFdeg m (fun g => σ (P⁻¹ * g * P)) d) : IsFdeg m (fun g => σ (P'⁻¹ * g * P')) d := by
  obtain ⟨hPu, hPJ⟩ := hP
  obtain ⟨hPu', hPJ'⟩ := hP'
  obtain ⟨⟨hσ1, hσmul⟩, hiso, -⟩ := hrep
  have h1 : σ (P'⁻¹ * 1 * P') = 1 := hσ1
  have hm : ∀ a ∈ UJset ε, ∀ b ∈ UJset ε,
      σ (P'⁻¹ * (a * b) * P') = (σ (P'⁻¹ * a * P')).comp (σ (P'⁻¹ * b * P')) := hσmul
  have hiso' : ∀ g ∈ UJset ε, ∀ x : H, ‖σ (P'⁻¹ * g * P') x‖ = ‖x‖ := hiso
  have hdet : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).1 hPu
  have hdet' : IsUnit P'.det := (Matrix.isUnit_iff_isUnit_det P').1 hPu'
  have hPPi : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hdet
  have hPPi' : P' * P'⁻¹ = 1 := Matrix.mul_nonsing_inv P' hdet'
  have hPiP' : P'⁻¹ * P' = 1 := Matrix.nonsing_inv_mul P' hdet'
  have hmem : ∀ A B : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ,
      Aᴴ * Formalism.REAL.Jm ε * A = Formalism.QuantumDeterminants.Hpk k r → Bᴴ * Formalism.REAL.Jm ε * B = Formalism.QuantumDeterminants.Hpk k r →
      B * B⁻¹ = 1 → A * B⁻¹ ∈ UJset ε := by
    intro A B hA hB hBB
    show (A * B⁻¹)ᴴ * Formalism.REAL.Jm ε * (A * B⁻¹) = Formalism.REAL.Jm ε
    have hB1 : (B⁻¹)ᴴ * Bᴴ = 1 := by
      rw [← Matrix.conjTranspose_mul, hBB, Matrix.conjTranspose_one]
    calc (A * B⁻¹)ᴴ * Formalism.REAL.Jm ε * (A * B⁻¹) = (B⁻¹)ᴴ * (Aᴴ * Formalism.REAL.Jm ε * A) * B⁻¹ := by
          rw [Matrix.conjTranspose_mul]
          simp only [Matrix.mul_assoc]
      _ = (B⁻¹)ᴴ * (Bᴴ * Formalism.REAL.Jm ε * B) * B⁻¹ := by rw [hA, hB]
      _ = ((B⁻¹)ᴴ * Bᴴ) * Formalism.REAL.Jm ε * (B * B⁻¹) := by simp only [Matrix.mul_assoc]
      _ = Formalism.REAL.Jm ε := by rw [hB1, hBB, Matrix.one_mul, Matrix.mul_one]
  have hQ : P * P'⁻¹ ∈ UJset ε := hmem P P' hPJ hPJ' hPPi'
  have hQi : P' * P⁻¹ ∈ UJset ε := hmem P' P hPJ' hPJ hPPi
  have hQQi : P * P'⁻¹ * (P' * P⁻¹) = 1 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc P'⁻¹, hPiP', Matrix.one_mul, hPPi]
  have hBC : ∀ x : H, σ (P'⁻¹ * (P * P'⁻¹) * P') (σ (P'⁻¹ * (P' * P⁻¹) * P') x) = x := by
    intro x
    have e := congrArg (fun T : H →L[ℂ] H => T x) (hm _ hQ _ hQi)
    simp only [ContinuousLinearMap.comp_apply, hQQi, h1, one_apply_eq_self] at e
    exact e.symm
  have hcoef : ∀ a b : H, coefOn (ε := ε) (fun g => σ (P'⁻¹ * g * P')) a b =
      coefOn (ε := ε) (fun g => σ (P⁻¹ * g * P)) (σ (P'⁻¹ * (P' * P⁻¹) * P') a)
        (σ (P'⁻¹ * (P' * P⁻¹) * P') b) := by
    intro a b
    funext g
    unfold coefOn
    beta_reduce
    have hg : umat g ∈ UJset ε := by exact g.2
    have hconj : P⁻¹ * umat g * P = P'⁻¹ * (P' * P⁻¹ * umat g * (P * P'⁻¹)) * P' := by
      simp only [← Matrix.mul_assoc, hPiP', Matrix.one_mul]
      rw [Matrix.mul_assoc _ P'⁻¹ P', hPiP', Matrix.mul_one]
    rw [hconj, hm _ (deg_UJ_mul hQi hg) _ hQ, hm _ hQi _ hg]
    simp only [ContinuousLinearMap.comp_apply]
    rw [hBC a, deg_inner_isom _ (hiso' _ hQi)]
  refine ⟨hd.1, fun v w v' w' => ?_⟩
  have hv := hd.2 (σ (P'⁻¹ * (P' * P⁻¹) * P') v) (σ (P'⁻¹ * (P' * P⁻¹) * P') w)
    (σ (P'⁻¹ * (P' * P⁻¹) * P') v') (σ (P'⁻¹ * (P' * P⁻¹) * P') w')
  rw [hcoef v w, hcoef v' w']
  refine ⟨hv.1, ?_⟩
  rw [hv.2, deg_inner_isom _ (hiso' _ hQi), deg_inner_isom _ (hiso' _ hQi)]

end Formalism.MainNotions.BridgeLemma₂

end
