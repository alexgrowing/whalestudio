import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeRingActsFaithfullyOnLocalisedLattice
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitsLiftSpec
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
open Formalism.L2.Fam.NPC Formalism.L2.Fam.NPC.BaseC GlobalTheory.HeckeLocN
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeRing_acts_faithfully_on_localisedLattice : ∀ {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (B : LocBase0 H what₂) (hs : HeckeStd0 B) (hd : FinDimV B), MtLoc B (partCompl_of hs hd) → HeckeIntTw B → SemisimpleTw B → ActEx B (partCompl_of hs hd) := by
  first | exact @GlobalTheory.HeckeLocAct.actEx_of | exact GlobalTheory.HeckeLocAct.actEx_of | (intros; apply GlobalTheory.HeckeLocAct.actEx_of <;> assumption)
