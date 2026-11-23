import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalBridgesAtPlacesOverResidueCharOfLargeCoeff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitsLiftSpec
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
open Formalism.L2.Fam.NPC Formalism.L2.Fam.NPC.BaseC GlobalTheory.HeckeLocN
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localBridges_at_placesOverResidueChar_of_large_coeff : ∀ (D : D7) (w : D.what₂.places.Pl), ∃ F0 : Loc.FinExt (D.what₂.places.resChar w), ∀ (X : CoefIn D.what₂) (j : ℕ), F0.1 ≤ (X.Kx j w).1 → BrAt X j w := by
  first | exact @GlobalTheory.HeckeLocN.BridgeAll.brAt_of_large | exact GlobalTheory.HeckeLocN.BridgeAll.brAt_of_large | (intros; apply GlobalTheory.HeckeLocN.BridgeAll.brAt_of_large <;> assumption)
