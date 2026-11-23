import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HighestWeightLineOfKTypeMultiplicityOne
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsOfIsDSPar
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible Formalism.L2.Theta Matrix GlobalTheory.RealPar GlobalTheory.CoverDS
open GlobalTheory.IndefiniteRowSideFullHecke.IsotypicSignedParameters (SignedPar IsDSPar)
open Formalism.MainNotions.S (IsURepOn IsIrredOn IsKFin IsKStableOn IsWtOn IsKTypeOf IsDS IsSqIntOn UJset)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.highestWeightLine_of_kTypeMultiplicityOne : ∀ (p q n : ℕ) (e : Ix p q ≃ Fin n) (ε : Fin n → Bool) (T : GrpData p q) (R : DSRep T) (σ : Matrix (Fin n) (Fin n) ℂ → (R.U.H →L[ℂ] R.U.H)), BlockOrd e ε → Factors R.U e σ → ∀ μ : Ix p q → ℚ, (∃ S, IsKTypeOf ε σ (fun i => (μ (e.symm i) : ℝ)) S) → (∀ S S', IsKTypeOf ε σ (fun i => (μ (e.symm i) : ℝ)) S → IsKTypeOf ε σ (fun i => (μ (e.symm i) : ℝ)) S' → S = S') → Module.finrank ℂ ↥(hwSub R.HK.act μ) = 1 := by
  first | exact @GlobalTheory.RealPar.HwLine.finrank_hwSub_eq_one | exact GlobalTheory.RealPar.HwLine.finrank_hwSub_eq_one | (intros; apply GlobalTheory.RealPar.HwLine.finrank_hwSub_eq_one <;> assumption)
