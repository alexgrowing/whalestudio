import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsOtherSplitPlaceWithDistinctRealPlace
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EqOneOfMemLev
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host
open GlobalTheory.HeckeUnrExt
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele (ideleMap ideleConj)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_other_split_place_with_distinct_real_place : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w₀ : HeightOneSpectrum (𝓞 E)), ∃ w₁ : HeightOneSpectrum (𝓞 E), GlobalTheory.UnitaryBC.IsSplitAt w₁ ∧ w₁.under (𝓞 (maximalRealSubfield E)) ≠ w₀.under (𝓞 (maximalRealSubfield E)) := by
  first | exact @GlobalTheory.OtherSplitPlace.exists_isSplitAt_under_ne | exact GlobalTheory.OtherSplitPlace.exists_isSplitAt_under_ne | (intros; apply GlobalTheory.OtherSplitPlace.exists_isSplitAt_under_ne <;> assumption)
