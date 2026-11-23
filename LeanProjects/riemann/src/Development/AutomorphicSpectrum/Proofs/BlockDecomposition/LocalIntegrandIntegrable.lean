import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.GaugeTopology.FComb
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.GaugeTopology.GTorus
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalFunctionalSectionTranslation
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalDoubleIntegralIdentity
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalHolomorphyInParameter

open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Filter Topology
open scoped ValuativeRel

namespace GlobalTheory.CompanionTheory.LFAbs

open Ad3 Ad3.LFS GlobalTheory.CompanionTheory.LFHolP

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]

theorem mp_one_ne_zero (x : Fˣ) : mp x 1 ≠ 0 := by
  have h : ((modulus (x : F) : ℝ) : ℂ) ≠ 0 := by
    have := GroundTheory.LocalField.modulus_ne_zero x.ne_zero
    exact_mod_cast this
  simpa [mp] using h

theorem continuous_integrand {ψ : AddChar F Circle} {W' : GL (Fin 2) F → ℂ}
    {Φ : Matrix (Fin 2) (Fin 3) F → ℂ}
    (hU : ∃ U : OpenSubgroup (GL (Fin 2) F), ∀ g, ∀ u ∈ U, W' (g * u) = W' g) (hΦ : Φ ∈ SB F) :
    Continuous fun h : GL (Fin 2) F =>
      W' h⁻¹ * mp (GeneralLinearGroup.det h) (3 / 2) * inn ψ Φ h 1 := by
  obtain ⟨U, hU⟩ := hU
  have hW : Continuous W' :=
    (GlobalTheory.CompanionTheory.RankinSelbergMellinContinuation.isLocallyConstant_of_invariant W' U.toSubgroup U.isOpen hU).continuous
  exact ((hW.comp continuous_inv).mul (continuous_mp_det _)).mul (cont_inn ψ Φ hΦ)

theorem integrable_one {ψ : AddChar F Circle} {ν : Fˣ →* ℂˣ} {W' : GL (Fin 2) F → ℂ}
    {Φ : Matrix (Fin 2) (Fin 3) F → ℂ} (hyp : Hyp ψ ν W' Φ) :
    Integrable (fun h : GL (Fin 2) F =>
      W' h⁻¹ * mp (GeneralLinearGroup.det h) (3 / 2) * inn ψ Φ h 1) (hG ψ) := by
  obtain ⟨hψ, hν, ⟨V', H, hW'⟩, hΦ⟩ := hyp
  obtain ⟨C, R, hCR⟩ := inn_bound hψ hΦ
  obtain ⟨C', hI⟩ := GlobalTheory.CompanionTheory.LFGInt2.gInt2 F ψ hψ ν hν V' H W' hW' R
  have hI1 := (hI 1 1).1
  have e2 : dg2 (1 : Fˣ) 1 = (1 : GL (Fin 2) F) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [dg2]
  have hC : 0 ≤ C :=
    le_trans (mul_nonneg (norm_nonneg _) (dk_pos (1 : GL (Fin 2) F)).le) (hCR 1).1
  refine (hI1.const_mul C).mono' (continuous_integrand (H.smooth W' hW') hΦ).aestronglyMeasurable
    (Eventually.of_forall fun h => ?_)
  have hd := dk_pos h
  by_cases hz : inn ψ Φ h 1 = 0
  · simp only [hz, mul_zero, norm_zero]
    exact mul_nonneg hC (Set.indicator_nonneg (fun k _ => by positivity) _)
  · have hm := (hCR h).2 hz
    rw [Set.indicator_of_mem hm, e2, one_mul, norm_mul, norm_mul, norm_mp_det]
    have h32 : dk h ^ (3 / 2 : ℂ).re = dk h ^ (1 / 2 : ℝ) * dk h := by
      have : (3 / 2 : ℂ).re = 1 / 2 + 1 := by norm_num
      rw [this, Real.rpow_add hd, Real.rpow_one]
    rw [h32]
    have hw : 0 ≤ ‖W' h⁻¹‖ * dk h ^ (1 / 2 : ℝ) := by positivity
    calc ‖W' h⁻¹‖ * (dk h ^ (1 / 2 : ℝ) * dk h) * ‖inn ψ Φ h 1‖
        = (‖W' h⁻¹‖ * dk h ^ (1 / 2 : ℝ)) * (‖inn ψ Φ h 1‖ * dk h) := by ring
      _ ≤ (‖W' h⁻¹‖ * dk h ^ (1 / 2 : ℝ)) * C := mul_le_mul_of_nonneg_left (hCR h).1 hw
      _ = C * (‖W' h⁻¹‖ * (modulus ((GeneralLinearGroup.det h : Fˣ) : F) : ℝ) ^ (1 / 2 : ℝ)) := by
          unfold dk
          ring

theorem integrable_wPhi : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (ψ : AddChar F Circle)
    (ν : Fˣ →* ℂˣ) (W' : GL (Fin 2) F → ℂ) (Φ : Matrix (Fin 2) (Fin 3) F → ℂ),
    Ad3.LFS.Hyp ψ ν W' Φ → ∀ g : GL (Fin 3) F,
    Integrable (fun h : GL (Fin 2) F =>
      W' h⁻¹ * Ad3.mp (GeneralLinearGroup.det h) (3 / 2) * Ad3.LFS.inn ψ Φ h g) (Ad3.LFS.hG ψ) := by
  intro F _ _ _ _ _ _ ψ ν W' Φ hyp g
  have hyp1 : Hyp ψ ν W' (rtr g Φ) :=
    ⟨hyp.1, hyp.2.1, hyp.2.2.1, GlobalTheory.CompanionTheory.LFTrans.rtr_mem_SB g hyp.2.2.2⟩
  have hne := mp_one_ne_zero (GeneralLinearGroup.det g)
  refine ((integrable_one hyp1).const_mul (mp (GeneralLinearGroup.det g) 1)⁻¹).congr
    (Eventually.of_forall fun h => ?_)
  simp only [GlobalTheory.CompanionTheory.LFTrans.inn_rtr, one_mul]
  field_simp

end GlobalTheory.CompanionTheory.LFAbs
