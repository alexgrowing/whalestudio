import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RankinSelbergKernelZeroCoeffTwoCentralChars
import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousOfMemSmoothSpan
import Development.AbelianVarietyTheory.Definitions.Divisors.MemMspan
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRapidInf
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsNormRsHatLeConst
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaIntegralUpperMspan
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousIntegralOfCompact
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SetIntegralRsHatZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspFormRapidKernelSmoothSpanSmoothCuspidalBound
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CuspRep GlobalTheory.UnitaryBC GroundTheory.Global.IdeleGroup Formalism.L2.Host
open scoped nonZeroDivisors ComplexConjugate

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rankinSelberg_kernel_zero_coeff_two_central_chars : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (ω ω' : HChar E), ω.IsUnitary → ω'.IsUnitary → ∀ (φ φ' : Sm E a), φ.1 ∈ GlobalTheory.Petersson.bddForms E a ω → φ'.1 ∈ GlobalTheory.Petersson.bddForms E a ω' → ∀ (ℓ : Fin a) (Φ : (Fin a → Cinf E) → ℂ), GlobalTheory.CuspQuot.IsTest (GlobalTheory.RSTheta.rowSet E ℓ) Φ → ∀ (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ) (η : Fin a → Af E), Continuous (fun g => GlobalTheory.RSThetaLow.rsHat ℓ φ.1 φ'.1 Φ J η g 0) ∧ (∃ C : ℝ, ∀ g, ‖GlobalTheory.RSThetaLow.rsHat ℓ φ.1 φ'.1 Φ J η g 0‖ ≤ C) ∧ (∀ (γ : GL (Fin a) E) (g : GA E a), GlobalTheory.RSThetaLow.rsHat ℓ φ.1 φ'.1 Φ J η (ratGL E a γ * g) 0 = GlobalTheory.RSThetaLow.rsHat ℓ φ.1 φ'.1 Φ J η g 0) ∧ ∀ (z : Neutral.B1.Ideles E) (g : GA E a), GlobalTheory.RSThetaLow.rsHat ℓ φ.1 φ'.1 Φ J η (GeneralLinearGroup.scalar (Fin a) z * g) 0 = ((ω.1 z : ℂˣ) : ℂ) * starRingEnd ℂ ((ω'.1 z : ℂˣ) : ℂ) * GlobalTheory.RSThetaLow.rsHat ℓ φ.1 φ'.1 Φ J η g 0 := by
  first | exact @GlobalTheory.RSResidue.rsHat_zero_props_two | exact GlobalTheory.RSResidue.rsHat_zero_props_two | (intros; apply GlobalTheory.RSResidue.rsHat_zero_props_two; all_goals assumption)
