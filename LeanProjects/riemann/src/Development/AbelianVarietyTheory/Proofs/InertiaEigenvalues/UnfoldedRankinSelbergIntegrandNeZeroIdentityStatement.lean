import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnfoldedRankinSelbergIntegrandNeZeroIdentity
import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocFacOfNeg
import Development.AbelianVarietyTheory.Definitions.Divisors.MemMspan
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRapidInf
import Development.AbelianVarietyTheory.Definitions.Divisors.UnrOutside
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW GroundTheory.Global.IdeleGroup Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal nonZeroDivisors Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unfoldedRankinSelbergIntegrand_ne_zero_identity : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (m : ℕ) (T : Finset (HeightOneSpectrum (𝓞 E)))
    (ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ) (F : GA E (m + 1) → ℂ) (Φ : (Fin (m + 1) → Cinf E) → ℂ)
    (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ) (l₀ : GlobalTheory.CellDec.abelian₂ E (m + 1) T), (∀ w, l₀.1 w (Fin.last m) = 0) →
    GlobalTheory.JSW.whit F (GlobalTheory.CellDec.tl (m + 1) ϖ l₀.1) ≠ 0 → Φ (Pi.single (Fin.last m) 1) ≠ 0 → ∀ x : ℝ, GlobalTheory.RSCell.bInt (Fin.last m) F Φ J (Pi.single (Fin.last m) 1) x (GlobalTheory.CellDec.tl (m + 1) ϖ l₀.1) ≠ 0 := by
  first | exact @GlobalTheory.RSCell.bInt_tl_last_ne_zero | exact GlobalTheory.RSCell.bInt_tl_last_ne_zero | (intros; apply GlobalTheory.RSCell.bInt_tl_last_ne_zero <;> assumption)
