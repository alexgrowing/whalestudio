import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EmbRelAtRealPlaceOfUnitaryEmbedding
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
theorem _root_.GlobalTheory.T.embRel_atRealPlace_of_unitaryEmbedding : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (A B : HSp D) (ι : A.V →ₗ[D.host.E] B.V) (τ : D.what₂.Tau)
    (h : Matrix (Fin A.rank) (Fin A.rank) ℂ) (g : Matrix (Fin B.rank) (Fin B.rank) ℂ), h ∈ Formalism.QuantumDeterminants.UH (gramAt D A τ) →
    g ∈ Formalism.QuantumDeterminants.UH (gramAt D B τ) → GlobalTheory.RealBessel.IsEmb (gramAt D B τ) ((frameMat B A ι).map (tauE D τ)) g h →
    EmbRel B A ι (atTau θ B τ g) (atTau θ A τ h) := by
  first | exact @GlobalTheory.EmbAtPlace.embRel_atTau | exact GlobalTheory.EmbAtPlace.embRel_atTau | (intros; apply GlobalTheory.EmbAtPlace.embRel_atTau <;> assumption)
