import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CasimirEqGelfandValueOfInfinitesimalCharacter
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsOfIsDSPar
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible Formalism.L2.Theta Matrix GlobalTheory.RealPar GlobalTheory.CoverDS
open GlobalTheory.IndefiniteRowSideFullHecke.IsotypicSignedParameters (SignedPar IsDSPar)
open Formalism.MainNotions.S (IsURepOn IsIrredOn IsKFin IsKStableOn IsWtOn IsKTypeOf IsDS IsSqIntOn UJset)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.casimir_eq_gelfandValue_of_infinitesimalCharacter : ∀ (p q n : ℕ) (e : Ix p q ≃ Fin n) (ε : Fin n → Bool) (T : GrpData p q) (R : DSRep T) (σ : Matrix (Fin n) (Fin n) ℂ → (R.U.H →L[ℂ] R.U.H)), BlockOrd e ε → Factors R.U e σ → ∀ χ : Fin n → ℂ, GlobalTheory.Dec.HasInfChar ε χ σ → ∀ v, casimir R.HK.act v = GlobalTheory.Dec.gelfVal χ 2 • v := by
  first | exact @GlobalTheory.CoverDS.casimir_eq_gelfVal_of_hasInfChar | exact GlobalTheory.CoverDS.casimir_eq_gelfVal_of_hasInfChar | (intros; apply GlobalTheory.CoverDS.casimir_eq_gelfVal_of_hasInfChar <;> assumption)
