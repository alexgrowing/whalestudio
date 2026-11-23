import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GTil
import GroundTheory.LocalFields.LocalFourierMult
import GroundTheory.LocalFields.LocalZetaTate
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData
open scoped ValuativeRel NNReal ENNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.GaussLam

section Subst

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem modulus_neg_eq (x : F) : modulus (-x) = modulus x := by
  have h1 : modulus (-1 : F) = 1 := by
    have h : modulus (-1 : F) * modulus (-1 : F) = 1 := by
      rw [← modulus_mul]; simp [modulus_one]
    have h2 : modulus (-1 : F) ^ 2 = 1 := by rw [sq]; exact h
    exact (pow_eq_one_iff_of_nonneg (by positivity) two_ne_zero).mp h2
  rw [← neg_one_mul, modulus_mul, h1, one_mul]

variable [MeasurableSpace F] [BorelSpace F]

theorem integral_haar_neg_inv (f : F → ℂ) :
    ∫ x, f x ∂haarIntegers F =
      ∫ a, ((modulus a : ℝ))⁻¹ • ((modulus a : ℝ))⁻¹ • f (-a⁻¹) ∂haarIntegers F := by
  haveI : (multHaar F).IsInvInvariant := Measure.IsHaarMeasure.isInvInvariant_of_regular (multHaar F)
  have hC : (multHaarConst F).toReal ≠ 0 :=
    ENNReal.toReal_ne_zero.mpr ⟨multHaarConst_ne_zero, multHaarConst_ne_top⟩
  have hres : (haarIntegers F).restrict ({0}ᶜ : Set F) = haarIntegers F :=
    Measure.restrict_eq_self_of_ae_mem (compl_mem_ae_iff.mpr haarIntegers_singleton_zero)
  have h1 := integral_multHaar (K := F) (fun x => (modulus x : ℝ) • f x)
  have h2 := integral_multHaar (K := F) (fun x => ((modulus x : ℝ))⁻¹ • f (-x⁻¹))
  rw [hres] at h1 h2
  have h3 : ∫ u : Fˣ, (modulus (u : F) : ℝ) • f (u : F) ∂multHaar F =
      ∫ u : Fˣ, ((modulus (u : F) : ℝ))⁻¹ • f (-(u : F)⁻¹) ∂multHaar F := by
    have e1 := integral_inv_eq_self (fun u : Fˣ =>
      (modulus (((-1 : Fˣ) * u : Fˣ) : F) : ℝ) • f (((-1 : Fˣ) * u : Fˣ) : F)) (multHaar F)
    have e2 := integral_mul_left_eq_self (μ := multHaar F)
      (fun u : Fˣ => (modulus (u : F) : ℝ) • f (u : F)) (-1 : Fˣ)
    rw [← e2, ← e1]
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    simp [modulus_neg_eq, modulus_inv]
  rw [h1, h2] at h3
  have h4 := smul_right_injective ℂ hC h3
  rw [← h4]
  refine integral_congr_ae ?_
  filter_upwards [compl_mem_ae_iff.mpr (haarIntegers_singleton_zero (K := F))] with x hx
  have hm : (modulus x : ℝ) ≠ 0 := by exact_mod_cast modulus_ne_zero hx
  rw [smul_smul, inv_mul_cancel₀ hm, one_smul]

end Subst

end GlobalTheory.CompanionTheory.GaussLam

open GlobalTheory.CompanionTheory.GaussLam in

theorem GlobalTheory.CompanionTheory.GaussLam.localFourier_gTil : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] [MeasurableSpace E] [BorelSpace E] [Algebra F E] [ValuativeExtension F E] [FiniteDimensional F E] [Algebra.IsSeparable F E] [Fact (Module.finrank F E = 2)] (χ : AddChar F Circle), Continuous χ → ∀ η : Fˣ →* ℂˣ, Continuous η → (∀ a : Fˣ, ((η a : ℂˣ) : ℂ) = nsg E (a : F)) → ∀ g : F → ℂ, g ∈ schwartzBruhat F → g 0 = 0 → ∀ t : F, localFourier (selfDualMeasure χ) χ (GlobalTheory.CompanionTheory.GaussLam.gTil E g) t = GlobalTheory.CompanionTheory.GaussLam.hAvg E χ g t := by
  intro F _ _ _ _ _ _ E _ _ _ _ _ _ _ _ _ _ _ χ _ η _ hη g _ _ t
  have hsq : ∀ a : F, a ≠ 0 → nsg E a⁻¹ = nsg E a := by
    intro a ha
    have h1 := hη (Units.mk0 a ha)
    have h2 := hη (Units.mk0 a ha)⁻¹
    simp only [Units.val_inv_eq_inv_val, Units.val_mk0, map_inv] at h1 h2
    rw [← h2, ← h1]
    have h3 : nsg E a = 1 ∨ nsg E a = -1 := by
      unfold nsg; split_ifs <;> simp
    rw [← h1] at h3
    rcases h3 with h3 | h3 <;> simp [h3]
  show ∫ x, gTil E g x * (χ (x * t) : ℂ) ∂selfDualMeasure χ = _
  rw [hAvg, selfDualMeasure, integral_smul_nnreal_measure, integral_smul_nnreal_measure,
    integral_haar_neg_inv]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
  by_cases ha : a = 0
  · subst ha
    simp [modulus_zero]
  have hm : (modulus a : ℝ) ≠ 0 := by exact_mod_cast modulus_ne_zero ha
  have e1 : -(-a⁻¹)⁻¹ = a := by simp
  have e2 : - -a⁻¹ = a⁻¹ := by simp
  have e3 : -a⁻¹ * t = -t / a := by field_simp
  simp only [gTil, e1, e2, e3, modulus_neg_eq, modulus_inv, hsq a ha, NNReal.coe_inv, inv_inv,
    Complex.real_smul]
  push_cast
  have hmc : ((modulus a : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hm
  field_simp
