import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlacesSameRealPlaceNatCastMem
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
theorem _root_.GlobalTheory.T.splitPlaces_same_realPlace_natCast_mem : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (s s' : SplitPlace L) (n : ℕ), s.v = s'.v →
    ((n : ℕ) : 𝓞 L) ∈ s.w.asIdeal → ((n : ℕ) : 𝓞 L) ∈ s'.w.asIdeal := by
  first | exact @GlobalTheory.split_places_same_natCast_mem | exact GlobalTheory.split_places_same_natCast_mem | (intros; apply GlobalTheory.split_places_same_natCast_mem <;> assumption)
