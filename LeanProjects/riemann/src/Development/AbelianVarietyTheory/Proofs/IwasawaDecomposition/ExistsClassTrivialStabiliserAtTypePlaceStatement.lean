import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsClassTrivialStabiliserAtTypePlace
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
theorem _root_.GlobalTheory.T.exists_class_trivial_stabiliser_at_typePlace : ∀ (D : D7) (k : Fin 2) (s : SplitPlace D.host.E), s.w ∈ placesOver D.host.E (D.host.g k) → ∃ g : GAf D.host.E D.R.nV, ∀ γ ∈ GQ D.host.E D.R.nV, g⁻¹ * γ * g ∈ Umax D.host.E D.R.nV → NG.UniRT s D.R.r (s.loc _ (g⁻¹ * γ * g)) → γ = 1 := by
  first | exact @GlobalTheory.NeatUni.exists_trivial_stabiliser | exact GlobalTheory.NeatUni.exists_trivial_stabiliser | (intros; apply GlobalTheory.NeatUni.exists_trivial_stabiliser <;> assumption)
