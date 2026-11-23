import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsTwiceDifferentiableAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.CompRightEqZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.KappaSt
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsFibreLocal
import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PDiagFibreFubini
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SphereMeasureStereographicIntegralStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.XiPotentialHessianDecompositionStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.MixedDiscriminantCofactorExpansionStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.EvalW
import Development.AutomorphicSpectrum.Proofs.MetricProofs.MixedDiscriminantLinearFunctionalStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.MixedDiscriminantTwoRowExpansionStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.MixedDiscriminantOneRowExpansionStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.WordCoefficientSecondDerivativeStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.RowProductFirstDerivativeStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ComplexHessianTwoPointCombinationStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ComplexHessianBlockCombinationStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SpherePairLogSineMomentStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SphereMomentPowerStatement
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights
open scoped ComplexOrder
open ReciprocityTheory.ChartRestriction.G.AI GroundTheory.Heights₂.Heights.Inter

namespace GlobalTheory.CompanionTheory.Ar.PB.FibN

noncomputable section

theorem densW (d k i : ℕ) (hi : i < k) (hkd : 2 * k ≤ d + 2) (T : Fin 3 → Matrix (Fin d) (Fin d) ℂ)
    (H : Matrix (Fin d) (Fin d) ℂ) (L : MvPolynomial (Option (Fin 3)) ℝ →ₗ[ℝ] ℂ)
    (hL : ∀ (c : Fin d → Fin 3 → ℝ) (v : Fin d → ℝ),
      (d.factorial : ℂ) * mdisc (fun t => (∑ i, ((c t i : ℝ) : ℂ) • T i) + ((v t : ℝ) : ℂ) • H) =
        L (∏ t, (lin4 (c t) + C (v t) * X none)))
    (f : (Fin (d + 1) → ℂ) → ℝ) (α : (Fin d → ℂ) → ℝ) (y : Fin d → ℂ)
    (hfc : ∀ a : ℂ, ContDiffAt ℝ 2 f (Fin.cons a y)) (hα : ContDiffAt ℝ 2 α y)
    (hfh : ∀ a : ℂ, hessC f (Fin.cons a y) = blk (-(wS a : ℂ)) (∑ j, ((nS a j : ℝ) : ℂ) • T j))
    (hH : H = hessC α y) (φ : Fin (d + 2) → (Fin (d + 2) → ℂ) → ℝ)
    (hφ : ∀ r z, φ r z =
      (if (r : ℕ) < 2 * k then DiagonalFibreFubini.wordCoef i r else 0 : Fin 2 → ℝ) 0 *
          f (Fin.cons (z 0) (Fin.tail (Fin.tail z))) +
        (if (r : ℕ) < 2 * k then DiagonalFibreFubini.wordCoef i r else 0 : Fin 2 → ℝ) 1 *
          f (Fin.cons (z 1) (Fin.tail (Fin.tail z))) +
        (if (r : ℕ) < 2 * k then (0 : ℝ) else 1) * α (Fin.tail (Fin.tail z)))
    (p₀ p₁ : ℂ) :
    maDens φ (Fin.cons p₀ (Fin.cons p₁ y)) = (2 / Real.pi) ^ (d + 2) * (wS p₀ * wS p₁ *
      (L (rename some (aeval ![lin3 (nS p₀), lin3 (nS p₁)]
        (pderiv 0 (pderiv 1 (wwLinProd k (DiagonalFibreFubini.wordCoef i))))) *
          X none ^ (d + 2 - 2 * k))).re) := by
  set uu : Fin (d + 2) → Fin 2 → ℝ := fun r => if (r : ℕ) < 2 * k then DiagonalFibreFubini.wordCoef i r else 0
  set vv : Fin (d + 2) → ℝ := fun r => if (r : ℕ) < 2 * k then (0 : ℝ) else 1
  have hrow : (fun r => hessC (φ r) (Fin.cons p₀ (Fin.cons p₁ y))) = fun r =>
      blk ((uu r 0 : ℂ) * -(wS p₀ : ℂ)) (blk ((uu r 1 : ℂ) * -(wS p₁ : ℂ))
        ((∑ j, ((uu r 0 * nS p₀ j + uu r 1 * nS p₁ j : ℝ) : ℂ) • T j) + ((vv r : ℝ) : ℂ) • H)) := by
    funext r
    have e : φ r = fun z : Fin (d + 2) → ℂ => uu r 0 * f (Fin.cons (z 0) (Fin.tail (Fin.tail z))) +
        uu r 1 * f (Fin.cons (z 1) (Fin.tail (Fin.tail z))) + vv r * α (Fin.tail (Fin.tail z)) :=
      funext (hφ r)
    rw [e, GlobalTheory.T.complex_hessian_two_point_combination d f α y p₀ p₁ _ _ _ _ (uu r 0) (uu r 1) (vv r) (hfc _) (hfc _) hα (hfh _) (hfh _), ← hH]
    congr 3
    simp only [Finset.smul_sum, smul_smul, ← Finset.sum_add_distrib, ← add_smul]
    refine Finset.sum_congr rfl fun j _ => ?_
    push_cast
    rfl
  have hB := GlobalTheory.T.mixed_discriminant_two_row_expansion d T H L hL uu vv (nS p₀) (nS p₁) (-(wS p₀ : ℂ)) (-(wS p₁ : ℂ))
  rw [GlobalTheory.T.word_coefficient_second_derivative d k i hi hkd (nS p₀) (nS p₁)] at hB
  rw [maDens, hrow]
  have hre := congrArg Complex.re hB
  rw [show (((d + 2).factorial : ℕ) : ℂ) = (((d + 2).factorial : ℝ) : ℂ) by push_cast; rfl,
    Complex.re_ofReal_mul, neg_mul_neg, ← Complex.ofReal_mul, Complex.re_ofReal_mul] at hre
  rw [mul_right_comm, hre]
  ring

theorem densY (d k : ℕ) (hk : 1 ≤ k) (hkd : 2 * k ≤ d + 2) (T : Fin 3 → Matrix (Fin d) (Fin d) ℂ)
    (H : Matrix (Fin d) (Fin d) ℂ) (L : MvPolynomial (Option (Fin 3)) ℝ →ₗ[ℝ] ℂ)
    (hL : ∀ (c : Fin d → Fin 3 → ℝ) (v : Fin d → ℝ),
      (d.factorial : ℂ) * mdisc (fun t => (∑ i, ((c t i : ℝ) : ℂ) • T i) + ((v t : ℝ) : ℂ) • H) =
        L (∏ t, (lin4 (c t) + C (v t) * X none)))
    (f : (Fin (d + 1) → ℂ) → ℝ) (α : (Fin d → ℂ) → ℝ) (y : Fin d → ℂ)
    (hfc : ∀ a : ℂ, ContDiffAt ℝ 2 f (Fin.cons a y)) (hα : ContDiffAt ℝ 2 α y)
    (hfh : ∀ a : ℂ, hessC f (Fin.cons a y) = blk (-(wS a : ℂ)) (∑ j, ((nS a j : ℝ) : ℂ) • T j))
    (hH : H = hessC α y) (φ : Fin (d + 1) → (Fin (d + 1) → ℂ) → ℝ)
    (hφ : ∀ r z, φ r z = (if (r : ℕ) < 2 * k - 1 then (1 : ℝ) else 0) * f z +
        (if (r : ℕ) < 2 * k - 1 then (0 : ℝ) else 1) * α (Fin.tail z))
    (a : ℂ) :
    maDens φ (Fin.cons a y) = (2 / Real.pi) ^ (d + 1) * (-(wS a) * (2 * (k : ℝ) - 1) *
      (L (rename some (lin3 (nS a) ^ (2 * k - 2)) * X none ^ (d + 2 - 2 * k))).re) := by
  set cc : Fin (d + 1) → ℝ := fun r => if (r : ℕ) < 2 * k - 1 then (1 : ℝ) else 0
  set vv : Fin (d + 1) → ℝ := fun r => if (r : ℕ) < 2 * k - 1 then (0 : ℝ) else 1
  have hrow : (fun r => hessC (φ r) (Fin.cons a y)) = fun r =>
      blk ((cc r : ℂ) * -(wS a : ℂ))
        ((∑ j, ((cc r * nS a j : ℝ) : ℂ) • T j) + ((vv r : ℝ) : ℂ) • H) := by
    funext r
    have e : φ r = fun z : Fin (d + 1) → ℂ => cc r * f z + vv r * α (Fin.tail z) := funext (hφ r)
    rw [e, GlobalTheory.T.complex_hessian_block_combination d f α y a _ _ (cc r) (vv r) (hfc _) hα (hfh _), ← hH]
    congr 2
    simp only [Finset.smul_sum, smul_smul]
    refine Finset.sum_congr rfl fun j _ => ?_
    push_cast
    rfl
  have hB := GlobalTheory.T.mixed_discriminant_one_row_expansion d T H L hL cc vv (nS a) (-(wS a : ℂ))
  rw [GlobalTheory.T.row_product_first_derivative d k hk hkd (nS a)] at hB
  rw [maDens, hrow]
  have hre := congrArg Complex.re hB
  have hR : (-(wS a : ℂ) * L (C (2 * (k : ℝ) - 1) * rename some (lin3 (nS a) ^ (2 * k - 2)) *
      X none ^ (d + 2 - 2 * k))).re = -(wS a) * (2 * (k : ℝ) - 1) *
        (L (rename some (lin3 (nS a) ^ (2 * k - 2)) * X none ^ (d + 2 - 2 * k))).re := by
    rw [mul_assoc (C _), C_mul', map_smul, Complex.real_smul, ← Complex.ofReal_neg, Complex.re_ofReal_mul,
      Complex.re_ofReal_mul]
    ring
  rw [show (((d + 1).factorial : ℕ) : ℂ) = (((d + 1).factorial : ℝ) : ℂ) by push_cast; rfl,
    Complex.re_ofReal_mul, hR] at hre
  rw [mul_right_comm, hre]
  ring

theorem fibre_integral_normal : GroundTheory.Heights₂.Heights.Inter.FibreLocal.Statement → ∀ (d k : ℕ), 1 ≤ k → 2 * k ≤ d + 2 → ∀ (G : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ) (α : (Fin d → ℂ) → ℝ) (y : Fin d → ℂ), (∀ᶠ y' in 𝓝 y, (G y').PosDef) → (∀ p q, ContDiffAt ℝ 2 (fun y' => G y' p q) y) → ContDiffAt ℝ 2 α y → G y = 1 → (∀ p q, fderiv ℝ (fun y' => G y' p q) y = 0) → (∑ i ∈ Finset.range k, ∫ p : ℂ × ℂ, logSin (G y) p.1 p.2 * maDens (let u : ℕ → Fin 2 → ℝ := (fun (i : ℕ) (r : ℕ) (c : Fin 2) => if r = 0 then (![1, -1] : Fin 2 → ℝ) c else if r = 1 then (![0, 1] : Fin 2 → ℝ) c else if r < 2 + 2 * i then (![1, 0] : Fin 2 → ℝ) c else (![0, 1] : Fin 2 → ℝ) c) i; (fun (r : Fin (d + 2)) (z : Fin (d + 2) → ℂ) => if (r : ℕ) < 2 * k then u r 0 * xiPot (G (Fin.tail (Fin.tail z))) (z 0) + u r 1 * xiPot (G (Fin.tail (Fin.tail z))) (z 1) else α (Fin.tail (Fin.tail z)))) (Fin.cons p.1 (Fin.cons p.2 y))) = 2 * ReciprocityTheory.ChartRestriction.G.AI.kappa k * ∫ a : ℂ, maDens (fun (r : Fin (d + 1)) (z : Fin (d + 1) → ℂ) => if (r : ℕ) < 2 * k - 1 then xiPot (G (Fin.tail z)) (z 0) else α (Fin.tail z)) (Fin.cons a y) := by
  intro h d k hk hkd G α y hPD hG2 hα hG1 hGd
  obtain ⟨T, hT⟩ := GlobalTheory.T.xi_potential_hessian_decomposition d G y hPD hG2 hG1 hGd
  obtain ⟨L, hL⟩ := GlobalTheory.T.mixed_discriminant_linear_functional d T (hessC α y)
  set f : (Fin (d + 1) → ℂ) → ℝ := fun z => xiPot (G (Fin.tail z)) (z 0) with hf
  have hfc : ∀ a : ℂ, ContDiffAt ℝ 2 f (Fin.cons a y) := fun a => (hT a).1
  have hfh : ∀ a : ℂ, hessC f (Fin.cons a y) = blk (-(wS a : ℂ)) (∑ j, ((nS a j : ℝ) : ℂ) • T j) := by
    intro a
    rw [(hT a).2]
    ext p q
    refine Fin.cases ?_ (fun p' => ?_) p <;> refine Fin.cases ?_ (fun q' => ?_) q
    · simp [blk, wS]
    · simp [blk]
    · simp [blk]
    · simp [blk, nS, Matrix.sum_apply]
  let ℓ : MvPolynomial (Fin 3) ℝ →ₗ[ℝ] ℝ := Complex.reLm ∘ₗ L ∘ₗ
    (LinearMap.mulRight ℝ (X none ^ (d + 2 - 2 * k) : MvPolynomial (Option (Fin 3)) ℝ)) ∘ₗ
      (rename some : MvPolynomial (Fin 3) ℝ →ₐ[ℝ] MvPolynomial (Option (Fin 3)) ℝ).toLinearMap
  have hℓ : ∀ p, (L (rename some p * X none ^ (d + 2 - 2 * k))).re = ℓ p := fun p => rfl
  have hword : ∀ i ∈ Finset.range k, (∫ p : ℂ × ℂ, logSin (G y) p.1 p.2 * maDens (let u : ℕ → Fin 2 → ℝ := (fun (i : ℕ) (r : ℕ) (c : Fin 2) => if r = 0 then (![1, -1] : Fin 2 → ℝ) c else if r = 1 then (![0, 1] : Fin 2 → ℝ) c else if r < 2 + 2 * i then (![1, 0] : Fin 2 → ℝ) c else (![0, 1] : Fin 2 → ℝ) c) i; (fun (r : Fin (d + 2)) (z : Fin (d + 2) → ℂ) => if (r : ℕ) < 2 * k then u r 0 * xiPot (G (Fin.tail (Fin.tail z))) (z 0) + u r 1 * xiPot (G (Fin.tail (Fin.tail z))) (z 1) else α (Fin.tail (Fin.tail z)))) (Fin.cons p.1 (Fin.cons p.2 y))) =
      (2 / Real.pi) ^ (d + 2) * (Real.pi ^ 2 * ℓ (diagWordMomentPoly k i)) := by
    intro i hi
    have hik := Finset.mem_range.1 hi
    have hpt : ∀ p : ℂ × ℂ, logSin (G y) p.1 p.2 * maDens (let u : ℕ → Fin 2 → ℝ := (fun (i : ℕ) (r : ℕ) (c : Fin 2) => if r = 0 then (![1, -1] : Fin 2 → ℝ) c else if r = 1 then (![0, 1] : Fin 2 → ℝ) c else if r < 2 + 2 * i then (![1, 0] : Fin 2 → ℝ) c else (![0, 1] : Fin 2 → ℝ) c) i; (fun (r : Fin (d + 2)) (z : Fin (d + 2) → ℂ) => if (r : ℕ) < 2 * k then u r 0 * xiPot (G (Fin.tail (Fin.tail z))) (z 0) + u r 1 * xiPot (G (Fin.tail (Fin.tail z))) (z 1) else α (Fin.tail (Fin.tail z)))) (Fin.cons p.1 (Fin.cons p.2 y)) =
        (2 / Real.pi) ^ (d + 2) * (logSin 1 p.1 p.2 * (wS p.1 * wS p.2 *
          ℓ (aeval ![lin3 (nS p.1), lin3 (nS p.2)]
            (pderiv 0 (pderiv 1 (wwLinProd k (DiagonalFibreFubini.wordCoef i))))))) := by
      intro p
      rw [densW d k i hik hkd T _ L hL f α y hfc hα hfh rfl _ ?_ p.1 p.2, hG1, hℓ]
      · ring
      · intro r z
        have hcoef : ∀ c : Fin 2, (if (r : ℕ) = 0 then (![1, -1] : Fin 2 → ℝ) c else if (r : ℕ) = 1 then (![0, 1] : Fin 2 → ℝ) c else if (r : ℕ) < 2 + 2 * i then (![1, 0] : Fin 2 → ℝ) c else (![0, 1] : Fin 2 → ℝ) c) = DiagonalFibreFubini.wordCoef i r c := by
          intro c
          simp only [DiagonalFibreFubini.wordCoef]
          split_ifs <;> rfl
        by_cases hr : (r : ℕ) < 2 * k
        · simp only [hr, if_true, hcoef, hf, Fin.tail, Fin.cons_zero, Fin.cons_succ]
          simp
        · simp [hr]
    simp_rw [hpt]
    rw [integral_const_mul, GlobalTheory.T.sphere_pair_log_sine_moment, DiagonalFibreFubini.linProd_word k i hik]
    rfl
  have hY : ∀ a : ℂ, maDens (fun (r : Fin (d + 1)) (z : Fin (d + 1) → ℂ) => if (r : ℕ) < 2 * k - 1 then xiPot (G (Fin.tail z)) (z 0) else α (Fin.tail z)) (Fin.cons a y) =
      (2 / Real.pi) ^ (d + 1) * (-(2 * (k : ℝ) - 1)) * (wS a * ℓ (lin3 (nS a) ^ (2 * k - 2))) := by
    intro a
    rw [densY d k hk hkd T _ L hL f α y hfc hα hfh rfl _ ?_ a, hℓ]
    · ring
    · intro r z
      by_cases hr : (r : ℕ) < 2 * k - 1
      · simp [hr, hf]
      · simp [hr]
  have hfib : fibreMomentPoly k = C (-kappa k) * (∑ i, X i ^ 2) ^ (k - 1) := by
    have h2 := h.2.1 k (MvPolynomial (Fin 3) ℝ) X
    rwa [aeval_X_left_apply, MvPolynomial.algebraMap_eq] at h2
  have hpush : pushMomentPoly k = -(∑ i, X i ^ 2) ^ (k - 1) := by
    have h2 := h.2.2.2.1 k hk (MvPolynomial (Fin 3) ℝ) X
    rwa [aeval_X_left_apply] at h2
  rw [Finset.sum_congr rfl hword, ← Finset.mul_sum, ← Finset.mul_sum, ← map_sum,
    DiagFibreMoment.sum_diagWordMomentPoly, hfib]
  simp_rw [hY]
  rw [integral_const_mul, GlobalTheory.T.sphere_moment_power]
  have hp : (-(2 * (k : ℝ) - 1)) * ℓ (momentPoly sphereMeasure (fun _ => 1) (dotPoly (id : S2 → S2) ^ (2 * k - 2))) =
      -ℓ ((∑ i, X i ^ 2) ^ (k - 1)) := by
    rw [← map_neg, ← hpush, pushMomentPoly, map_smul, smul_eq_mul]
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  rw [C_mul', map_smul, smul_eq_mul]
  calc _ = (2 / Real.pi) ^ (d + 1) * (2 / Real.pi) * Real.pi ^ 2 * (-kappa k * ℓ ((∑ i, X i ^ 2) ^ (k - 1))) := by
        rw [pow_succ]; ring
    _ = 2 * kappa k * ((2 / Real.pi) ^ (d + 1) * (Real.pi * (-ℓ ((∑ i, X i ^ 2) ^ (k - 1))))) := by
        field_simp
    _ = _ := by
        rw [← hp]; ring

end

end GlobalTheory.CompanionTheory.Ar.PB.FibN
