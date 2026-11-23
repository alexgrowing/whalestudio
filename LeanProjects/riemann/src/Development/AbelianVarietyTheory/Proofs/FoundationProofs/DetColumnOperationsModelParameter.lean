import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.TheoremOfCubeOfAdditionFormulas
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OddThetaFunctionExistenceUniqueness
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DifferentiableSqTh
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TaylorSeriesInParameterRescaleOfAlgebraic
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SigmaStarSquareQuotientInModelParameter
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ColA
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators
open PowerSeries
namespace GlobalTheory.FrobStick

theorem det_column_alg {R : Type*} [CommRing R] (x e w q : Fin 3 → R) (ε r a₁ a₃ S D1 D2 D3 : R)
    (hq : ∀ i, q i * w i = 1) (hu : IsUnit (2 * ε ^ 4))
    (h : Matrix.det (Matrix.of fun i j => (![ε ^ 3 * x i ^ 3 * e i ^ 3,
      ε * e i ^ 3 * (x i * q i + ε ^ 2 * r * x i ^ 3),
      e i ^ 3 * q i * (a₁ * x i + a₃ * x i ^ 3 * w i - 2)] : Fin 3 → R) j) =
      2 * (ε * S) * (ε * D1) * (ε * D2) * (ε * D3)) :
    (x 0 ^ 3 * w 0 * (x 2 - x 1) + x 1 ^ 3 * w 1 * (x 0 - x 2) + x 2 ^ 3 * w 2 * (x 1 - x 0))
      * e 0 ^ 3 * e 1 ^ 3 * e 2 ^ 3 = w 0 * w 1 * w 2 * S * D1 * D2 * D3 := by
  have hrow : ∀ i, e i ^ 3 * q i * (a₁ * x i + a₃ * x i ^ 3 * w i - 2)
      = e i ^ 3 * (a₁ * x i * q i + a₃ * x i ^ 3 - 2 * q i) := fun i => by
    linear_combination e i ^ 3 * a₃ * x i ^ 3 * hq i
  simp only [hrow] at h
  rw [Matrix.det_fin_three] at h
  simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] at h
  have h2 : 2 * ε ^ 4 * (e 0 ^ 3 * e 1 ^ 3 * e 2 ^ 3 *
      (x 0 ^ 3 * (q 1 * q 2) * (x 2 - x 1) + x 1 ^ 3 * (q 0 * q 2) * (x 0 - x 2)
        + x 2 ^ 3 * (q 0 * q 1) * (x 1 - x 0))) = 2 * ε ^ 4 * (S * D1 * D2 * D3) := by
    linear_combination h
  have h3 := hu.mul_left_cancel h2
  have h12 : q 1 * q 2 * (w 1 * w 2) = 1 := by
    rw [mul_mul_mul_comm, hq, hq, one_mul]
  have h02 : q 0 * q 2 * (w 0 * w 2) = 1 := by
    rw [mul_mul_mul_comm, hq, hq, one_mul]
  have h01 : q 0 * q 1 * (w 0 * w 1) = 1 := by
    rw [mul_mul_mul_comm, hq, hq, one_mul]
  linear_combination w 0 * w 1 * w 2 * h3
    - e 0 ^ 3 * e 1 ^ 3 * e 2 ^ 3 * (x 0 ^ 3 * w 0 * (x 2 - x 1) * h12
      + x 1 ^ 3 * w 1 * (x 0 - x 2) * h02 + x 2 ^ 3 * w 2 * (x 1 - x 0) * h01)

theorem det_column_ops : ∀ (p : ℕ) [Fact p.Prime] (E wq : PowerSeries ℂ_[p]) (ε r a₁ a₃ : ℂ_[p]) (s d₁ d₂ d₃ : MvPowerSeries (Fin 3) ℂ_[p]), ε ≠ 0 → PowerSeries.constantCoeff wq = 1 → MvPowerSeries.constantCoeff s = 0 → MvPowerSeries.constantCoeff d₁ = 0 → MvPowerSeries.constantCoeff d₂ = 0 → MvPowerSeries.constantCoeff d₃ = 0 → Matrix.det (Matrix.of fun i j => (PowerSeries.subst (GL3Theta.Xv i : MvPowerSeries (Fin 3) ℂ_[p]) (![PowerSeries.C (ε ^ 3) * PowerSeries.X ^ 3 * E ^ 3, PowerSeries.C ε * E ^ 3 * (PowerSeries.X * wq⁻¹ + PowerSeries.C (ε ^ 2 * r) * PowerSeries.X ^ 3), E ^ 3 * wq⁻¹ * (PowerSeries.C a₁ * PowerSeries.X + PowerSeries.C a₃ * PowerSeries.X ^ 3 * wq - 2)] j) : MvPowerSeries (Fin 3) ℂ_[p])) = 2 * PowerSeries.subst s (PowerSeries.C ε * PowerSeries.X * E) * PowerSeries.subst d₁ (PowerSeries.C ε * PowerSeries.X * E) * PowerSeries.subst d₂ (PowerSeries.C ε * PowerSeries.X * E) * PowerSeries.subst d₃ (PowerSeries.C ε * PowerSeries.X * E) → ((GL3Theta.Xv 0) ^ 3 * PowerSeries.subst (GL3Theta.Xv 0 : MvPowerSeries (Fin 3) ℂ_[p]) wq * (GL3Theta.Xv 2 - GL3Theta.Xv 1) + (GL3Theta.Xv 1) ^ 3 * PowerSeries.subst (GL3Theta.Xv 1 : MvPowerSeries (Fin 3) ℂ_[p]) wq * (GL3Theta.Xv 0 - GL3Theta.Xv 2) + (GL3Theta.Xv 2) ^ 3 * PowerSeries.subst (GL3Theta.Xv 2 : MvPowerSeries (Fin 3) ℂ_[p]) wq * (GL3Theta.Xv 1 - GL3Theta.Xv 0)) * PowerSeries.subst (GL3Theta.Xv 0 : MvPowerSeries (Fin 3) ℂ_[p]) E ^ 3 * PowerSeries.subst (GL3Theta.Xv 1 : MvPowerSeries (Fin 3) ℂ_[p]) E ^ 3 * PowerSeries.subst (GL3Theta.Xv 2 : MvPowerSeries (Fin 3) ℂ_[p]) E ^ 3 = PowerSeries.subst (GL3Theta.Xv 0 : MvPowerSeries (Fin 3) ℂ_[p]) wq * PowerSeries.subst (GL3Theta.Xv 1 : MvPowerSeries (Fin 3) ℂ_[p]) wq * PowerSeries.subst (GL3Theta.Xv 2 : MvPowerSeries (Fin 3) ℂ_[p]) wq * (s * PowerSeries.subst s E) * (d₁ * PowerSeries.subst d₁ E) * (d₂ * PowerSeries.subst d₂ E) * (d₃ * PowerSeries.subst d₃ E) := by
  intro p _ E wq ε r a₁ a₃ s d₁ d₂ d₃ hε hw hs h1 h2 h3 h
  have hC : ∀ (a : MvPowerSeries (Fin 3) ℂ_[p]), HasSubst a → ∀ c : ℂ_[p],
      PowerSeries.subst a (PowerSeries.C c : PowerSeries ℂ_[p]) = MvPowerSeries.C c := by
    intro a ha c
    rw [← coe_substAlgHom ha]
    exact (substAlgHom ha).commutes c
  have hlin : ∀ (a : MvPowerSeries (Fin 3) ℂ_[p]), MvPowerSeries.constantCoeff a = 0 →
      PowerSeries.subst a (PowerSeries.C ε * PowerSeries.X * E) =
        MvPowerSeries.C ε * (a * PowerSeries.subst a E) := by
    intro a ha
    have ha' : HasSubst a := HasSubst.of_constantCoeff_zero ha
    rw [subst_mul ha', subst_mul ha', hC a ha', subst_X ha', mul_assoc]
  have hX : ∀ i : Fin 3, HasSubst (GL3Theta.Xv i : MvPowerSeries (Fin 3) ℂ_[p]) := fun i =>
    HasSubst.of_constantCoeff_zero (by simp [GL3Theta.Xv])
  rw [hlin s hs, hlin d₁ h1, hlin d₂ h2, hlin d₃ h3] at h
  refine det_column_alg (fun i => (GL3Theta.Xv i : MvPowerSeries (Fin 3) ℂ_[p]))
    (fun i => PowerSeries.subst (GL3Theta.Xv i : MvPowerSeries (Fin 3) ℂ_[p]) E)
    (fun i => PowerSeries.subst (GL3Theta.Xv i : MvPowerSeries (Fin 3) ℂ_[p]) wq)
    (fun i => PowerSeries.subst (GL3Theta.Xv i : MvPowerSeries (Fin 3) ℂ_[p]) wq⁻¹)
    (MvPowerSeries.C ε) (MvPowerSeries.C r) (MvPowerSeries.C a₁) (MvPowerSeries.C a₃) _ _ _ _
    ?_ ?_ ?_
  · intro i
    rw [← subst_mul (hX i), PowerSeries.inv_mul_cancel _ (by rw [hw]; exact one_ne_zero),
      ← coe_substAlgHom (hX i), map_one]
  · have : (2 * MvPowerSeries.C ε ^ 4 : MvPowerSeries (Fin 3) ℂ_[p]) =
        MvPowerSeries.C (2 * ε ^ 4) := by
      rw [map_mul, map_pow, map_ofNat]
    rw [this]
    exact (IsUnit.mk0 _ (mul_ne_zero two_ne_zero (pow_ne_zero _ hε))).map _
  · rw [← h]
    congr 1
    ext1 i j
    have hCi := hC _ (hX i)
    have hXi := subst_X (R := ℂ_[p]) (hX i)
    rw [← coe_substAlgHom (hX i)] at hCi hXi
    simp only [Matrix.of_apply]
    rw [← coe_substAlgHom (hX i)]
    fin_cases j
    all_goals
      simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val, map_mul, map_pow, map_add, map_sub, map_ofNat, hCi, hXi]

end GlobalTheory.FrobStick
