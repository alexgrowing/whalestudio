import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PadNatZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RsTermZero
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ZintZero
import Development.AbelianVarietyTheory.Definitions.Divisors.MemMspan
import Development.AbelianVarietyTheory.Definitions.Divisors.UnrOutside
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRapidInf
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAddHaarMeasureVolumeLie
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SchurDir
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicUnitriangularMulMemUnipotentTimesIntegral
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import GroundTheory.AutomorphicForms.MultiplicityOne.Injective
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnfoldMirabolic
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LintegralThetaSeriesUnfoldMirabolic
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPsiLocNeOne
open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW Formalism.UG GlobalTheory.LFun Formalism.L2.Host
open scoped ENNReal ComplexConjugate ContDiff
open GlobalTheory.MirTower GlobalTheory.CuspGeneric
open GroundTheory.Automorphic.FourierWhittaker (partialCoeff blockGL uGL)

namespace GlobalTheory.RSnm

open GroundTheory.Automorphic.FourierWhittaker (partialCoeff_self partialCoeff_of_lt stepCoeff
  colGL_eq_blockGL whittaker_eq_partialCoeff continuous_partialCoeff)

theorem partialCoeff_partialCoeff_comp_blockGL {E : Type} [Field E] [NumberField E] {a n : ℕ}
    (han : a ≤ n) (φ : GA E n → ℂ) :
    ∀ (d j : ℕ), j + d = a → ∀ h : GA E a,
      partialCoeff (fun h : GA E a => partialCoeff φ a (blockGL han h)) j h =
        partialCoeff φ j (blockGL han h) := by
  intro d
  induction d with
  | zero =>
    intro j hj h
    obtain rfl : j = a := by omega
    rw [partialCoeff_self]
  | succ d ih =>
    intro j hj h
    have hja : j < a := by omega
    rw [partialCoeff_of_lt _ hja, partialCoeff_of_lt φ (hja.trans_le han)]
    unfold stepCoeff
    congr 1
    funext x
    rw [ih (j + 1) (by omega), map_mul, ← colGL_eq_blockGL hja han]

theorem whit_partialCoeff_comp_blockGL : ∀ (E : Type) [Field E] [NumberField E] (k m : ℕ) (hmk : m + 1 ≤ k) (φ : GA E (k + 1) → ℂ),
    Continuous φ → ∀ h : GA E (m + 1),
    GlobalTheory.JSW.whit (fun h => partialCoeff φ (m + 1) (blockGL (by omega : m + 1 ≤ k + 1) h)) h =
      GlobalTheory.JSW.whit φ (blockGL (by omega : m + 1 ≤ k + 1) h) := by
  intro E _ _ k m hmk φ hφ h
  have hb : m + 1 ≤ k + 1 := by omega
  have hQ : Continuous fun h : GA E (m + 1) => partialCoeff φ (m + 1) (blockGL hb h) :=
    (continuous_partialCoeff hφ (m + 1)).comp (GlobalTheory.RSnm.continuous_blockGL hb)
  unfold GlobalTheory.JSW.whit
  rw [whittaker_eq_partialCoeff hQ (Nat.succ_pos m), whittaker_eq_partialCoeff hφ (Nat.succ_pos k)]
  exact partialCoeff_partialCoeff_comp_blockGL hb φ m 1 (by omega) h

end GlobalTheory.RSnm
