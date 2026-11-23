import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.ThetaConstantWeber
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.ThetaLine
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.DifferentiableOddTheta

open Complex
open scoped Real

noncomputable section

namespace GlobalTheory.ThetaWeberRoad

theorem exp_half_pi_I : cexp ((π : ℂ) * I / 2) = I := by
  rw [show (π : ℂ) * I / 2 = π / 2 * I by ring]
  exact Complex.exp_pi_div_two_mul_I

theorem exp_neg_half_pi_I : cexp (-((π : ℂ) * I / 2)) = -I := by
  rw [show -((π : ℂ) * I / 2) = -π / 2 * I by ring]
  exact Complex.exp_neg_pi_div_two_mul_I

theorem neg_cexp (x : ℂ) : -cexp x = cexp ((π : ℂ) * I + x) := by
  rw [Complex.exp_add, Complex.exp_pi_mul_I, neg_one_mul]

theorem I_mul_cexp (x : ℂ) : I * cexp x = cexp ((π : ℂ) * I / 2 + x) := by
  rw [Complex.exp_add, exp_half_pi_I]

theorem negI_mul_cexp (x : ℂ) : -I * cexp x = cexp (-((π : ℂ) * I / 2) + x) := by
  rw [Complex.exp_add, exp_neg_half_pi_I]

theorem thetaConst_zero_zero (τ : UpperHalfPlane) :
    GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber.thetaConst 0 0 τ = jacobiTheta₂ 0 τ := by
  simp [GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber.thetaConst]

theorem thetaConst_zero_one (τ : UpperHalfPlane) :
    GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber.thetaConst 0 1 τ = jacobiTheta₂ (1 / 2) τ := by
  simp [GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber.thetaConst]

theorem thetaConst_one_zero (τ : UpperHalfPlane) :
    GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber.thetaConst 1 0 τ =
      cexp ((π : ℂ) * I * (τ : ℂ) / 4) * jacobiTheta₂ ((τ : ℂ) / 2) τ := by
  unfold GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber.thetaConst
  push_cast
  congr 2 <;> ring

theorem oddTheta_eq_of (τ : UpperHalfPlane) (z w k : ℂ)
    (h : jacobiTheta₂ (z + ((τ : ℂ) + 1) / 2) τ = cexp k * jacobiTheta₂ w τ) :
    oddTheta τ z = cexp ((π : ℂ) * I * (τ : ℂ) / 4 + π * I * (z + 1 / 2) + k) * jacobiTheta₂ w τ := by
  unfold oddTheta
  rw [h, ← mul_assoc, ← Complex.exp_add]

theorem oddTheta_half (τ : UpperHalfPlane) :
    oddTheta τ (1 / 2) = -GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber.thetaConst 1 0 τ := by
  have h : jacobiTheta₂ (1 / 2 + ((τ : ℂ) + 1) / 2) τ = cexp 0 * jacobiTheta₂ ((τ : ℂ) / 2) τ := by
    rw [show (1 : ℂ) / 2 + ((τ : ℂ) + 1) / 2 = (τ : ℂ) / 2 + 1 by ring, jacobiTheta₂_add_left,
      Complex.exp_zero, one_mul]
  rw [oddTheta_eq_of τ _ _ _ h, thetaConst_one_zero, ← neg_mul, neg_cexp]
  congr 2
  ring

theorem oddTheta_tau_half (τ : UpperHalfPlane) :
    oddTheta τ ((τ : ℂ) / 2) =
      -I * cexp (-((π : ℂ) * I * (τ : ℂ) / 4)) * GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber.thetaConst 0 1 τ := by
  have h : jacobiTheta₂ ((τ : ℂ) / 2 + ((τ : ℂ) + 1) / 2) τ =
      cexp (-π * I * ((τ : ℂ) + 2 * (1 / 2))) * jacobiTheta₂ (1 / 2) τ := by
    rw [show (τ : ℂ) / 2 + ((τ : ℂ) + 1) / 2 = 1 / 2 + (τ : ℂ) by ring, jacobiTheta₂_add_left']
  rw [oddTheta_eq_of τ _ _ _ h, thetaConst_zero_one, negI_mul_cexp]
  congr 2
  ring

theorem oddTheta_one_add_tau_half (τ : UpperHalfPlane) :
    oddTheta τ ((1 + (τ : ℂ)) / 2) =
      -cexp (-((π : ℂ) * I * (τ : ℂ) / 4)) * GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber.thetaConst 0 0 τ := by
  have h : jacobiTheta₂ ((1 + (τ : ℂ)) / 2 + ((τ : ℂ) + 1) / 2) τ =
      cexp (-π * I * (τ : ℂ)) * jacobiTheta₂ 0 τ := by
    rw [show (1 + (τ : ℂ)) / 2 + ((τ : ℂ) + 1) / 2 = (0 + 1) + (τ : ℂ) by ring, jacobiTheta₂_add_left',
      jacobiTheta₂_add_left]
    congr 1
    rw [show -(π : ℂ) * I * ((τ : ℂ) + 2 * (0 + 1)) = -π * I * (τ : ℂ) - 2 * π * I by ring,
      Complex.exp_sub, Complex.exp_two_pi_mul_I, div_one]
  rw [oddTheta_eq_of τ _ _ _ h, thetaConst_zero_zero, neg_cexp]
  congr 2
  ring

theorem oddTheta_one_sub_tau_half (τ : UpperHalfPlane) :
    oddTheta τ (1 / 2 - (τ : ℂ) / 2) =
      -cexp (-((π : ℂ) * I * (τ : ℂ) / 4)) * GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber.thetaConst 0 0 τ := by
  have h : jacobiTheta₂ (1 / 2 - (τ : ℂ) / 2 + ((τ : ℂ) + 1) / 2) τ = cexp 0 * jacobiTheta₂ 0 τ := by
    rw [show (1 : ℂ) / 2 - (τ : ℂ) / 2 + ((τ : ℂ) + 1) / 2 = 0 + 1 by ring, jacobiTheta₂_add_left,
      Complex.exp_zero, one_mul]
  rw [oddTheta_eq_of τ _ _ _ h, thetaConst_zero_zero, neg_cexp]
  congr 2
  ring

theorem oddTheta_one_add_tau_half' (τ : UpperHalfPlane) :
    oddTheta τ (1 + (τ : ℂ) / 2) =
      I * cexp (-((π : ℂ) * I * (τ : ℂ) / 4)) * GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber.thetaConst 0 1 τ := by
  have h : jacobiTheta₂ (1 + (τ : ℂ) / 2 + ((τ : ℂ) + 1) / 2) τ =
      cexp (-π * I * ((τ : ℂ) + 2 * (1 / 2))) * jacobiTheta₂ (1 / 2) τ := by
    rw [show 1 + (τ : ℂ) / 2 + ((τ : ℂ) + 1) / 2 = (1 / 2 + (τ : ℂ)) + 1 by ring, jacobiTheta₂_add_left,
      jacobiTheta₂_add_left']
  rw [oddTheta_eq_of τ _ _ _ h, thetaConst_zero_one, I_mul_cexp]
  congr 2
  ring

theorem oddTheta_neg_tau_half (τ : UpperHalfPlane) :
    oddTheta τ (-((τ : ℂ) / 2)) =
      I * cexp (-((π : ℂ) * I * (τ : ℂ) / 4)) * GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber.thetaConst 0 1 τ := by
  have h : jacobiTheta₂ (-((τ : ℂ) / 2) + ((τ : ℂ) + 1) / 2) τ = cexp 0 * jacobiTheta₂ (1 / 2) τ := by
    rw [show -((τ : ℂ) / 2) + ((τ : ℂ) + 1) / 2 = 1 / 2 by ring, Complex.exp_zero, one_mul]
  rw [oddTheta_eq_of τ _ _ _ h, thetaConst_zero_one, I_mul_cexp]
  congr 2
  ring

theorem oddTheta_half_add_tau (τ : UpperHalfPlane) :
    oddTheta τ (1 / 2 + (τ : ℂ)) =
      -(cexp (-((π : ℂ) * I * (τ : ℂ))) * GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber.thetaConst 1 0 τ) := by
  have h : jacobiTheta₂ (1 / 2 + (τ : ℂ) + ((τ : ℂ) + 1) / 2) τ =
      cexp (-π * I * ((τ : ℂ) + 2 * ((τ : ℂ) / 2))) * jacobiTheta₂ ((τ : ℂ) / 2) τ := by
    rw [show 1 / 2 + (τ : ℂ) + ((τ : ℂ) + 1) / 2 = ((τ : ℂ) / 2 + (τ : ℂ)) + 1 by ring,
      jacobiTheta₂_add_left, jacobiTheta₂_add_left']
  rw [oddTheta_eq_of τ _ _ _ h, thetaConst_one_zero, ← mul_assoc, ← Complex.exp_add, ← neg_mul, neg_cexp]
  congr 2
  ring

private theorem g_add_mul_g_sub_of_addition_laws (E g σ : ℂ → ℂ) (c Δ z w : ℂ)
    (hE : E (z + w) * E (z - w) = E z ^ 2 * E w ^ 2) (hz : E z ≠ 0) (hw : E w ≠ 0)
    (hI : ∀ u, E u * g u = c * σ u) (hσ : σ (z + w) * σ (z - w) = -(σ z ^ 2 * σ w ^ 2 * Δ)) :
    c ^ 2 * (g (z + w) * g (z - w)) = -(g z ^ 2 * g w ^ 2 * Δ) := by
  have h0 : E z ^ 2 * E w ^ 2 ≠ 0 := mul_ne_zero (pow_ne_zero _ hz) (pow_ne_zero _ hw)
  apply mul_left_cancel₀ h0
  have h1 := hI (z + w)
  have h2 := hI (z - w)
  have h3 := hI z
  have h4 := hI w
  calc E z ^ 2 * E w ^ 2 * (c ^ 2 * (g (z + w) * g (z - w)))
      = c ^ 2 * ((E (z + w) * g (z + w)) * (E (z - w) * g (z - w))) := by rw [← hE]; ring
    _ = c ^ 4 * (σ (z + w) * σ (z - w)) := by rw [h1, h2]; ring
    _ = -((c * σ z) ^ 2 * (c * σ w) ^ 2 * Δ) := by rw [hσ]; ring
    _ = -((E z * g z) ^ 2 * (E w * g w) ^ 2 * Δ) := by rw [h3, h4]
    _ = E z ^ 2 * E w ^ 2 * -(g z ^ 2 * g w ^ 2 * Δ) := by ring

theorem oddTheta_addition (hSA : Formalism.L2.Th1.F.SgStarAdd) (τ : UpperHalfPlane)
    (hI : ∀ z : ℂ, Complex.exp ((Real.pi : ℂ) * z ^ 2 / (2 * ((τ.im : ℝ) : ℂ))) * oddTheta τ z =
      deriv (oddTheta τ) 0 * Formalism.L2.Th1.F.sgStar (GlobalTheory.periodPairOfTau τ) z)
    (z w : ℂ) (hz : z ∉ (GlobalTheory.periodPairOfTau τ).lattice) (hw : w ∉ (GlobalTheory.periodPairOfTau τ).lattice) :
    deriv (oddTheta τ) 0 ^ 2 * (oddTheta τ (z + w) * oddTheta τ (z - w)) =
      -(oddTheta τ z ^ 2 * oddTheta τ w ^ 2 *
        (GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber.wp τ z - GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber.wp τ w)) := by
  have hσ := hSA (GlobalTheory.periodPairOfTau τ) z w hz hw
  unfold GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber.wp
  refine g_add_mul_g_sub_of_addition_laws (fun u => Complex.exp ((Real.pi : ℂ) * u ^ 2 / (2 * ((τ.im : ℝ) : ℂ))))
    (oddTheta τ) (Formalism.L2.Th1.F.sgStar (GlobalTheory.periodPairOfTau τ)) _ _ z w ?_ (Complex.exp_ne_zero _)
    (Complex.exp_ne_zero _) hI hσ
  simp only [← Complex.exp_add, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

private theorem d_eq_sq_mul_pow_four_of_relations (p A B C g c e d1 d2 d3 : ℂ) (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0)
    (hc : c ≠ 0) (hg : g ^ 2 = p ^ 2 * (A * B * C) ^ 2) (hc4 : c ^ 4 = e)
    (e1 : g ^ 2 * (-c * A * (-c * A)) = -((-C) ^ 2 * (-I * c * B) ^ 2 * d1))
    (e2 : g ^ 2 * (I * c * B * (I * c * B)) = -((-C) ^ 2 * (-c * A) ^ 2 * d2))
    (e3 : g ^ 2 * (-(e * C) * -C) = -((-c * A) ^ 2 * (-I * c * B) ^ 2 * d3)) :
    d1 = p ^ 2 * A ^ 4 ∧ d2 = p ^ 2 * B ^ 4 ∧ d3 = p ^ 2 * C ^ 4 := by
  rw [hg] at e1 e2 e3
  rw [← hc4] at e3
  have hI2 : I ^ 2 = -1 := Complex.I_sq
  refine ⟨?_, ?_, ?_⟩
  · have h : (c ^ 2 * B ^ 2 * C ^ 2) * d1 = (c ^ 2 * B ^ 2 * C ^ 2) * (p ^ 2 * A ^ 4) := by
      linear_combination (-1 : ℂ) * e1 + C ^ 2 * c ^ 2 * B ^ 2 * d1 * hI2
    exact mul_left_cancel₀ (by simp [hc, hB, hC]) h
  · have h : (c ^ 2 * A ^ 2 * C ^ 2) * d2 = (c ^ 2 * A ^ 2 * C ^ 2) * (p ^ 2 * B ^ 4) := by
      linear_combination e2 - p ^ 2 * A ^ 2 * B ^ 4 * C ^ 2 * c ^ 2 * hI2
    exact mul_left_cancel₀ (by simp [hc, hA, hC]) h
  · have h : (c ^ 4 * A ^ 2 * B ^ 2) * d3 = (c ^ 4 * A ^ 2 * B ^ 2) * (p ^ 2 * C ^ 4) := by
      linear_combination (-1 : ℂ) * e3 + c ^ 4 * A ^ 2 * B ^ 2 * d3 * hI2
    exact mul_left_cancel₀ (by simp [hc, hA, hB]) h

theorem halfPeriodDiff_of : Formalism.L2.Th1.F.SgStarAdd →
    (∀ (τ : UpperHalfPlane) (z : ℂ), Complex.exp ((Real.pi : ℂ) * z ^ 2 / (2 * ((τ.im : ℝ) : ℂ))) *
      GlobalTheory.ThetaWeberRoad.oddTheta τ z =
        deriv (GlobalTheory.ThetaWeberRoad.oddTheta τ) 0 * Formalism.L2.Th1.F.sgStar (GlobalTheory.periodPairOfTau τ) z) →
    (∀ τ : UpperHalfPlane, HasDerivAt (GlobalTheory.ThetaWeberRoad.oddTheta τ)
      (-2 * (Real.pi : ℂ) * ModularForm.eta (τ : ℂ) ^ 3) 0) →
    (∀ τ : UpperHalfPlane, GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber.JacobiProduct τ) →
    ∀ τ : UpperHalfPlane, GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber.HalfPeriodDiff τ := by
  intro hSA hI hD hJ τ
  obtain ⟨n1, n2, n3⟩ := GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber.halfPeriods_notMem τ
  have hd : deriv (oddTheta τ) 0 = -2 * (Real.pi : ℂ) * ModularForm.eta (τ : ℂ) ^ 3 := (hD τ).deriv
  have hJ' : GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber.thetaConst 0 0 τ * GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber.thetaConst 0 1 τ *
      GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber.thetaConst 1 0 τ = 2 * ModularForm.eta (τ : ℂ) ^ 3 := hJ τ
  have hη : ModularForm.eta (τ : ℂ) ≠ 0 := ModularForm.eta_ne_zero τ.2
  have hABC : GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber.thetaConst 0 0 τ * GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber.thetaConst 0 1 τ *
      GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber.thetaConst 1 0 τ ≠ 0 := by
    rw [hJ']
    exact mul_ne_zero two_ne_zero (pow_ne_zero _ hη)
  have hA : GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber.thetaConst 0 0 τ ≠ 0 := fun h => hABC (by rw [h]; ring)
  have hB : GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber.thetaConst 0 1 τ ≠ 0 := fun h => hABC (by rw [h]; ring)
  have hC : GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber.thetaConst 1 0 τ ≠ 0 := fun h => hABC (by rw [h]; ring)
  have hg : deriv (oddTheta τ) 0 ^ 2 = (π : ℂ) ^ 2 * (GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber.thetaConst 0 0 τ *
      GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber.thetaConst 0 1 τ * GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber.thetaConst 1 0 τ) ^ 2 := by
    rw [hd, hJ']
    ring
  have hc4 : cexp (-((π : ℂ) * I * (τ : ℂ) / 4)) ^ 4 = cexp (-((π : ℂ) * I * (τ : ℂ))) := by
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have e1 := oddTheta_addition hSA τ (hI τ) (1 / 2) ((τ : ℂ) / 2) n1 n2
  have e2 := oddTheta_addition hSA τ (hI τ) (1 / 2) ((1 + (τ : ℂ)) / 2) n1 n3
  have e3 := oddTheta_addition hSA τ (hI τ) ((1 + (τ : ℂ)) / 2) ((τ : ℂ) / 2) n3 n2
  rw [show (1 : ℂ) / 2 + (τ : ℂ) / 2 = (1 + (τ : ℂ)) / 2 by ring] at e1
  rw [show (1 : ℂ) / 2 + (1 + (τ : ℂ)) / 2 = 1 + (τ : ℂ) / 2 by ring,
    show (1 : ℂ) / 2 - (1 + (τ : ℂ)) / 2 = -((τ : ℂ) / 2) by ring] at e2
  rw [show (1 + (τ : ℂ)) / 2 + (τ : ℂ) / 2 = 1 / 2 + (τ : ℂ) by ring,
    show (1 + (τ : ℂ)) / 2 - (τ : ℂ) / 2 = 1 / 2 by ring] at e3
  rw [oddTheta_one_add_tau_half, oddTheta_one_sub_tau_half, oddTheta_half, oddTheta_tau_half] at e1
  rw [oddTheta_one_add_tau_half', oddTheta_neg_tau_half, oddTheta_half, oddTheta_one_add_tau_half] at e2
  rw [oddTheta_half_add_tau, oddTheta_half, oddTheta_one_add_tau_half, oddTheta_tau_half] at e3
  exact d_eq_sq_mul_pow_four_of_relations _ _ _ _ _ _ _ _ _ _ hA hB hC (Complex.exp_ne_zero _) hg hc4 e1 e2 e3

end GlobalTheory.ThetaWeberRoad
