import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SiegelEisensteinContinuationAndPoles
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.EisRegularAtOfEisPoleLE
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegel_eisenstein_continuation_and_poles : GlobalTheory.Published.CuspRapidDecay → (∀ (D : D7) (V : HSp D), 0 < V.rank → ∀ a : GL (Fin V.rank) (AE D), IsMaj V a → HasIwasawa D.sp.cm.sig (dblSp V).gram (Khat V a) → ∀ (μ : (AE D)ˣ →* Circle) (b : ℕ), IsHeckeChar D μ → ResEta D μ b → ∀ (s₁ : ℂ) (φ : GA D (dblSp V) → ℂ), φ ∈ degPS V a μ s₁ → (GlobalTheory.Eis.EisContinues V (flat V a φ s₁) ∧ ∀ s₀, ∃ k, GlobalTheory.Eis.EisRegularAt V (flat V a φ s₁) s₀ k) ∧ (V.rank < b → GlobalTheory.Eis.EisPoleLE V (flat V a φ s₁) (((b : ℂ) - V.rank) / 2) 1)) → GlobalTheory.Published.DoublingMethod := by
  first | exact @GlobalTheory.Eis.doublingMethod_of_eisenstein | exact GlobalTheory.Eis.doublingMethod_of_eisenstein | (intros; apply GlobalTheory.Eis.doublingMethod_of_eisenstein <;> assumption)
