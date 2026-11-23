import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAnalyticNonvanishingDenominator
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaOn
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.Doubling GlobalTheory.ThK.Bot
open Formalism.L2.Host (aboveF)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_analytic_nonvanishing_denominator : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) (T : Finset (Pl F)),
    ∃ D : ℂ → ℂ, AnalyticOnNhd ℂ D {s | 0 < s.re} ∧ ∀ s : ℂ, 0 < s.re → D s ≠ 0 ∧ HasProd (fun v : {v : Pl F // v ∉ T} => denInv E n v.1 s) (D s) := by
  first | exact @GlobalTheory.ThK.Bot.DenProd.exists_hasProd_denInv | exact GlobalTheory.ThK.Bot.DenProd.exists_hasProd_denInv | (intros; apply GlobalTheory.ThK.Bot.DenProd.exists_hasProd_denInv <;> assumption)
