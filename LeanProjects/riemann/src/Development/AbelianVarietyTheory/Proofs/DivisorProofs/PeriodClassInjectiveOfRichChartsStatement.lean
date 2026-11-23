import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodClassInjectiveOfRichCharts
import Development.AbelianVarietyTheory.Definitions.Divisors.EllFamNontrivial
import Development.AbelianVarietyTheory.Definitions.Divisors.FstTszeSec
open CategoryTheory GlobalTheory.CatCoh GlobalTheory.AnPer GlobalTheory.AnPer.Charts TopologicalSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.periodClass_injective_of_rich_charts : ∀ {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} (K : Charts F), K.Rich → ∀ per per' : Λ →+ Hol F.V, K.perCl per = K.perCl per' → per = per' := by
  first | exact @GlobalTheory.AnPer.Charts.perCl_injective | exact GlobalTheory.AnPer.Charts.perCl_injective | (intros; apply GlobalTheory.AnPer.Charts.perCl_injective <;> assumption)
