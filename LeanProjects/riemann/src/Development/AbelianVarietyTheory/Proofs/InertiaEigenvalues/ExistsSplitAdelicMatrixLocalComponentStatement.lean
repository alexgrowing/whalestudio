import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSplitAdelicMatrixLocalComponent
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnipotentBlockColumnIndex
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.CuspGeneric
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_split_adelicMatrix_localComponent : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (w : HeightOneSpectrum (𝓞 E)) (g : GA E a), ∃ (h : GA E a) (gw : GL (Fin a) (w.adicCompletion E)), g = h * finGL E a (locGL E a w gw) ∧ ∀ u : GL (Fin a) (w.adicCompletion E), h * finGL E a (locGL E a w u) = finGL E a (locGL E a w u) * h := by
  first | exact @GlobalTheory.CuspGeneric.exists_split_loc | exact GlobalTheory.CuspGeneric.exists_split_loc | (intros; apply GlobalTheory.CuspGeneric.exists_split_loc <;> assumption)
