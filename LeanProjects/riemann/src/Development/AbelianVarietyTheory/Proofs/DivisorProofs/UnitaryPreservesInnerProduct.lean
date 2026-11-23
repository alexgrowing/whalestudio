import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzMemL2

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.L2PairingPolar

theorem integral_mul_conj_eq_inner {X : Type} [MeasurableSpace X] {μ : Measure X} {u v : X → ℂ}
    (hu : MemLp u 2 μ) (hv : MemLp v 2 μ) :
    ∫ x, u x * starRingEnd ℂ (v x) ∂μ = inner ℂ hv.toLp hu.toLp := by
  rw [MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hu.coeFn_toLp, hv.coeFn_toLp] with x hx hy
  rw [hx, hy]
  simp [mul_comm]

theorem eLpNorm_two_eq {X : Type} [MeasurableSpace X] {μ : Measure X} {u v : X → ℂ}
    (h : ∫⁻ x, ‖u x‖ₑ ^ 2 ∂μ = ∫⁻ x, ‖v x‖ₑ ^ 2 ∂μ) : eLpNorm u 2 μ = eLpNorm v 2 μ := by
  have h2 : (2 : ENNReal) ≠ 0 := by norm_num
  rw [eLpNorm_eq_lintegral_rpow_enorm h2 ENNReal.ofNat_ne_top,
    eLpNorm_eq_lintegral_rpow_enorm h2 ENNReal.ofNat_ne_top]
  simp only [ENNReal.toReal_ofNat, ENNReal.rpow_two]
  rw [h]

theorem pairing_eq : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (T : Module.End ℂ ((κ → AF F) → ℂ)),
    (∀ φ ∈ schA F κ, T φ ∈ schA F κ) →
    (∀ μ : @Measure (κ → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ → ∀ φ ∈ schA F κ,
      ∫⁻ x, ‖T φ x‖ₑ ^ 2 ∂μ = ∫⁻ x, ‖φ x‖ₑ ^ 2 ∂μ) →
    ∀ μ : @Measure (κ → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ → ∀ f ∈ schA F κ, ∀ g ∈ schA F κ,
      ∫ x, T f x * starRingEnd ℂ (T g x) ∂μ = ∫ x, f x * starRingEnd ℂ (g x) ∂μ := by
  intro F _ _ κ _ T hpres hiso
  letI : MeasurableSpace (κ → AF F) := borel _
  intro μ hμ f hf g hg
  have hmem : ∀ φ ∈ schA F κ, MemLp φ 2 μ := fun φ hφ => GlobalTheory.WeilM.schA_memLp_two F κ μ hμ φ hφ
  have hf2 := hmem f hf
  have hg2 := hmem g hg
  have hTf2 := hmem (T f) (hpres f hf)
  have hTg2 := hmem (T g) (hpres g hg)
  rw [integral_mul_conj_eq_inner hTf2 hTg2, integral_mul_conj_eq_inner hf2 hg2]
  have hN : ∀ c : ℂ, ‖hTg2.toLp + c • hTf2.toLp‖ = ‖hg2.toLp + c • hf2.toLp‖ := by
    intro c
    have hw : g + c • f ∈ schA F κ := (schA F κ).add_mem hg ((schA F κ).smul_mem c hf)
    have h := eLpNorm_two_eq (hiso μ hμ _ hw)
    rw [map_add, map_smul] at h
    rw [← MemLp.toLp_const_smul, ← MemLp.toLp_add, ← MemLp.toLp_const_smul, ← MemLp.toLp_add,
      Lp.norm_toLp, Lp.norm_toLp, h]
  have e1 : ‖hTg2.toLp + hTf2.toLp‖ = ‖hg2.toLp + hf2.toLp‖ := by simpa using hN 1
  have e2 : ‖hTg2.toLp - hTf2.toLp‖ = ‖hg2.toLp - hf2.toLp‖ := by
    simpa [sub_eq_add_neg] using hN (-1)
  have e3 : ‖hTg2.toLp + (RCLike.I : ℂ) • hTf2.toLp‖ = ‖hg2.toLp + (RCLike.I : ℂ) • hf2.toLp‖ := hN _
  have e4 : ‖hTg2.toLp - (RCLike.I : ℂ) • hTf2.toLp‖ = ‖hg2.toLp - (RCLike.I : ℂ) • hf2.toLp‖ := by
    have := hN (-(RCLike.I : ℂ))
    simpa only [neg_smul, ← sub_eq_add_neg] using this
  rw [inner_eq_sum_norm_sq_div_four, inner_eq_sum_norm_sq_div_four, e1, e2, e3, e4]

end GlobalTheory.L2PairingPolar
