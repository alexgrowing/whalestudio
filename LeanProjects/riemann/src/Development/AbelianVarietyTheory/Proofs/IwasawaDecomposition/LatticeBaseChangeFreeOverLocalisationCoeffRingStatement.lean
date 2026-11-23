import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LatticeBaseChangeFreeOverLocalisationCoeffRing
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitsLiftSpec
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
open Formalism.L2.Fam.NPC Formalism.L2.Fam.NPC.BaseC GlobalTheory.HeckeLocN
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.latticeBaseChange_free_over_localisation_coeffRing : ∀ (D : D7) (B : LocBase0 D.host D.what₂) (hI : OsInt B), (Function.Injective D.what₂.OtoLL ∧ ∃ F : Subfield D.what₂.LL, ∀ x, x ∈ D.what₂.OtoLL.range ↔ x ∈ F ∧ IsIntegral ℤ x) → ∀ i, Module.Free (OOf B i) (BjC B hI i) := by
  first | exact @GlobalTheory.BjFree.bjC_free | exact GlobalTheory.BjFree.bjC_free | (intros; apply GlobalTheory.BjFree.bjC_free <;> assumption)
