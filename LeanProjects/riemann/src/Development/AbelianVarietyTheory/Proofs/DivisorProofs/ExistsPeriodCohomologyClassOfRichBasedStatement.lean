import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPeriodCohomologyClassOfRichBased
import Development.AbelianVarietyTheory.Definitions.Divisors.EllFamNontrivial
import Development.AbelianVarietyTheory.Definitions.Divisors.FstTszeSec
open CategoryTheory GlobalTheory.CatCoh GlobalTheory.AnPer GlobalTheory.AnPer.Charts TopologicalSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_period_cohomologyClass_of_rich_based : ∀ {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} (K : Charts F), K.Rich → K.Based → ∀ c : H1 K.Oc, ∃ per : Λ →+ Hol F.V, c = K.perCl per := by
  first | exact @GlobalTheory.AnPer.Charts.exists_perCl | exact GlobalTheory.AnPer.Charts.exists_perCl | (intros; apply GlobalTheory.AnPer.Charts.exists_perCl <;> assumption)
