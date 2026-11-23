import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.QuotientAverageTranslateInvariant
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnipotentBlockColumnIndex
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.CuspGeneric
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quotientAverage_translate_invariant : ∀ (G : Type) [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] (Γ : AddSubgroup G), IsCoLat Γ → ∀ Φ : G → ℂ, Per Γ Φ → ∀ y : G, avg Γ (fun x => Φ (x + y)) = avg Γ Φ := by
  first | exact @GlobalTheory.CuspGeneric.avg_add_right | exact GlobalTheory.CuspGeneric.avg_add_right | (intros; apply GlobalTheory.CuspGeneric.avg_add_right <;> assumption)
