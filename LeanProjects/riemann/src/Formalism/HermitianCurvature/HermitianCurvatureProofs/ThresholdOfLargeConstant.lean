import Formalism.HermitianCurvature.LemmaDensOfSteps
import Formalism.HermitianCurvature.StatementJF
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LUFactorOrbitBounds
import Formalism.HermitianCurvature.HermitianCurvatureProofs.AdjointnessPolynomiallyBounded
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BigCellVanishingOfCommute

open Matrix MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C6

theorem xi_eq_xiTau_one_one {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (p : B.SS k r) :
    JF.xiP D p = B.xiTau D (1, 1) p := by
  have hs : ∀ x : ℝ, star (Complex.exp (Complex.I * (x : ℂ))) = Complex.exp (-(Complex.I * (x : ℂ))) := by
    intro x
    show (starRingEnd ℂ) (Complex.exp (Complex.I * (x : ℂ))) = _
    rw [← Complex.exp_conj]
    congr 1
    simp [Complex.conj_ofReal]
  simp only [JF.xiP, B.xiTau, psi, B.lam, hs]
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem threshold_of_large_constant {k r CV : ℕ} {A : ℝ} (hr : 1 ≤ r) (hCV : 19 ≤ CV)
    (hA : (r : ℝ) * AV CV r (2 * r + k + 1) ≤ A) : JF.TransportedAlt k r A 0 := by
  unfold JF.TransportedAlt
  unfold AV at hA
  have hr' : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hCV' : (19 : ℝ) ≤ CV := by exact_mod_cast hCV
  have hn1 : (1 : ℝ) ≤ ((2 * r + k + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ 2 * r + k + 1)
  simp only [Nat.cast_zero, mul_zero, sub_zero]
  rw [lt_div_iff₀ (by positivity)]
  have h1 : (r : ℝ) * ((CV : ℝ) * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2) ≤ A := by
    refine le_trans ?_ hA
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have : 0 ≤ (r : ℝ) ^ 3 * ((2 * r + k + 1 : ℕ) : ℝ) := by positivity
    have : 0 ≤ (r : ℝ) ^ 4 := by positivity
    linarith
  have h2 : (r : ℝ) * (19 * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2) ≤
      (r : ℝ) * ((CV : ℝ) * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact mul_le_mul_of_nonneg_right hCV' (by positivity)
  have h3 : 0 ≤ ((r : ℝ) - 1) * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 :=
    mul_nonneg (by linarith) (sq_nonneg _)
  have h4 : 0 < (r : ℝ) * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 := by positivity
  nlinarith

theorem big_cell_density_of_parts : Formalism.FourierDecayAlt.DensityAveraging.DensBigOfParts := by
  intro hR
  refine ⟨19, ?_⟩
  intro CV hCV k r Wp Wq _ _ _ _ _ _ D A ε mm F' γ H hγ hrel O
  obtain ⟨hr, hε, hA, hmm, hF, hsupp, hbig⟩ := H
  have hRs : Rset γ = {1} := hR k r Wp Wq D γ hγ hrel
  have hconc : O.μR ({(1 : B.Mat k r)} : Set (Mt k r))ᶜ = 0 := by
    have := O.haarR.conc
    rw [hRs] at this
    exact this
  have hone : O.μR ({(1 : B.Mat k r)} : Set (Mt k r)) < ⊤ :=
    O.haarR.finite_compact _ isCompact_singleton
  have hfin : O.μR Set.univ < ⊤ := by
    calc O.μR Set.univ = O.μR (({(1 : B.Mat k r)} : Set (Mt k r)) ∪ ({(1 : B.Mat k r)} : Set (Mt k r))ᶜ) := by
          rw [Set.union_compl_self]
      _ ≤ O.μR ({(1 : B.Mat k r)} : Set (Mt k r)) + O.μR ({(1 : B.Mat k r)} : Set (Mt k r))ᶜ := measure_union_le _ _
      _ < ⊤ := by rw [hconc, add_zero]; exact hone
  have hne : O.μR Set.univ ≠ 0 := Measure.measure_univ_ne_zero.mpr O.haarR.ne_zero
  set c : ℝ := O.μR.real Set.univ with hc_def
  have hc : 0 < c := by
    rw [hc_def, measureReal_def]; exact ENNReal.toReal_pos hne hfin.ne
  have hγOm : γ ∈ JF.Om k r D.z D.z' := ⟨hγ.1, fun l _ => hγ.2.2 l (Finset.mem_univ _), hγ.2.1⟩
  have hThr : JF.TransportedAlt k r A 0 := threshold_of_large_constant hr hCV hA
  have hint0 := (bessel_integral_converges k r Wp Wq D A F' hThr (DifferentialOperatorClasses.inCC_mono (Nat.zero_le mm) hF)).1 γ hγOm
  have hθ : ∀ p : B.SS k r, D.inSS p →
      ∫ x, (fun _ : B.SS k r => c⁻¹) (actR γ (Matrix.of x) p) ∂O.μR = 1 := by
    intro p _
    simp only [integral_const, smul_eq_mul]
    rw [← hc_def]; field_simp
  have hfun : (fun p : B.SS k r => (fun _ : B.SS k r => c⁻¹) p • (B.xiTau D (1, 1) p • B.rho D p F' γ)) =
      fun p => c⁻¹ • JF.integrand D F' γ p := by
    funext p; simp only [JF.integrand, xi_eq_xiTau_one_one]
  have hint : Integrable (fun p : B.SS k r => (fun _ : B.SS k r => c⁻¹) p • (B.xiTau D (1, 1) p • B.rho D p F' γ))
      D.μSS := by
    rw [hfun]; exact hint0.smul c⁻¹
  have hw := O.weil F' (fun _ => c⁻¹) measurable_const (fun _ => by positivity) hθ hint
  rw [← hw, integral_smul]
  have hJ : ∫ p, B.xiTau D (1, 1) p • B.rho D p F' γ ∂D.μSS = 0 := by
    have h1 : B.Jtau D (1, 1) F' γ = B.JF D F' γ := bessel_function_trivial_index k r Wp Wq D F' γ
    rw [hbig γ hγ] at h1
    exact h1
  rw [hJ, smul_zero]

end Formalism.FourierDecayAlt.P
