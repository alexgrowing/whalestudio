import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFullLevelMeasure
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OneMeasureSizes
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TamagawaSpecialUnitary
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.FWT GlobalTheory.CovTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_full_level_measure : ∀ (D : D7) (Tu : Type) (Cl : LevCh D Tu) (t0 : Tu), Cl.Is t0 → ∀ (i : Fin D.R.m) (P : LevelP Cl.Pg D.R.r ℂ) (μ : MeasureTheory.Measure (Formalism.L2.Theta.GA D (Wc D i))) (𝓕 : Set (Formalism.L2.Theta.GA D (Wc D i))), Formalism.IndefR.Lev.IsMeasFD (Wc D i) (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.levW Cl i P) μ 𝓕 → ∃ μ' : MeasureTheory.Measure (Formalism.L2.Theta.GA D (Wc D i)), Formalism.IndefR.Lev.IsMeasFD (Wc D i) (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.levW Cl i (LevelP.full Cl.Pg D.R.r ℂ)) μ' 𝓕 ∧ μ' 𝓕 ≤ μ 𝓕 := by
  first | exact @GlobalTheory.MassFullLevel.mass_le_of_full | exact GlobalTheory.MassFullLevel.mass_le_of_full | (intros; apply GlobalTheory.MassFullLevel.mass_le_of_full <;> assumption)
