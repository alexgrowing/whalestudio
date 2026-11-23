import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AtRealPlaceMemUnipotentFlagAdelic
import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ParRowZero
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselPeriodCorankConvergesColumn
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselPeriodRightTranslateSobolevSepContinuous
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Mi.SepPer (contLeft)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.atRealPlace_mem_unipotentFlag_adelic : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (B : HSp D) {ρ : ℕ} (e : Matrix (Fin B.rank) (Fin ρ) D.host.E) (τ : D.what₂.Tau)
    (u : Matrix (Fin B.rank) (Fin B.rank) ℂ), u ∈ GlobalTheory.RealBessel.unipRad (gramAt D B τ) (e.map (tauE D τ)) →
    atTau θ B τ u ∈ NFlag B e := by
  first | exact @GlobalTheory.FlagRealUnip.atTau_mem_NFlag | exact GlobalTheory.FlagRealUnip.atTau_mem_NFlag | (intros; apply GlobalTheory.FlagRealUnip.atTau_mem_NFlag <;> assumption)
