import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistedTupleFiniteOrderPartUnramifiedAtTypePrime
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReadsHecke
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedTuple_finiteOrderPart_unramified_at_typePrimes : ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (v : B.places.Pl) (Q : HeightOneSpectrum (𝓞 B.host.E)) (k : Fin 2),
    ((B.host.g k : ℕ) : 𝓞 B.host.E) ∈ Q.asIdeal → Q ∉ T.Q v → (T.xiTw f v).UnrAt Q := by
  first | exact @GlobalTheory.TwistUnr.unrAt_xiTw | exact GlobalTheory.TwistUnr.unrAt_xiTw | (intros; apply GlobalTheory.TwistUnr.unrAt_xiTw <;> assumption)
