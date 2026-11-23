import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistConductorsOverRealPlacesAndConjStable
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitsLiftSpec
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
open Formalism.L2.Fam.NPC Formalism.L2.Fam.NPC.BaseC GlobalTheory.HeckeLocN
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistConductors_over_real_places_and_conj_stable : ∀ (D : D7) (cf : CharFrame D) (C : NChoice D) (tp : TupTied D cf C), (∀ w, ¬ TwistedAt D w → C.Q w = ∅) → QOver C ∧ QConj C := by
  first | exact @GlobalTheory.HeckeLocN.CondConj.cond_over_conj | exact GlobalTheory.HeckeLocN.CondConj.cond_over_conj | (intros; apply GlobalTheory.HeckeLocN.CondConj.cond_over_conj <;> assumption)
