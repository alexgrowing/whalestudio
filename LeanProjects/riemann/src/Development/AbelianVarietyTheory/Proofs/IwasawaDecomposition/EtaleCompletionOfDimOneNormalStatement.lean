import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EtaleCompletionOfDimOneNormal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TraitOrdOfTraitOrdPt
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef GlobalTheory.Cartier
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etale_completion_of_dim_one_normal : ∀ {A R : Type} [CommRing A] [IsLocalRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A] [CommRing R] [IsDomain R] [IsLocalRing R] (φ : A →+* R), ringKrullDim A = 1 → IsEtaleCompletion φ → IsCN R → CDvr R := by
  first | exact @GlobalTheory.CdvrExt.cdvr_of_isEtaleCompletion | exact GlobalTheory.CdvrExt.cdvr_of_isEtaleCompletion | (intros; apply GlobalTheory.CdvrExt.cdvr_of_isEtaleCompletion <;> assumption)
