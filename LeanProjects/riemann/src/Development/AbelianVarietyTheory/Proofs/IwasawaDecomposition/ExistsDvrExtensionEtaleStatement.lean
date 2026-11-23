import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsDvrExtensionEtale
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TraitOrdOfTraitOrdPt
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef GlobalTheory.Cartier
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_dvr_extension_etale : ∀ {A R W : Type} [CommRing A] [IsLocalRing A] [CommRing R] [IsDomain R] [IsLocalRing R] [CommRing W] [IsDomain W] [IsLocalRing W] (φ : A →+* R) (ψ : A →+* W), IsCN R → IsEtaleCompletion φ → ((residue R).comp φ).FormallyUnramified → CDvr W → IsLocalHom ψ → ∃ (W' : Type) (_ : CommRing W') (_ : IsDomain W') (_ : IsLocalRing W') (ι : W →+* W') (g : R →+* W'), CDvr W' ∧ (∀ ϖ : W, Irreducible ϖ → Irreducible (ι ϖ)) ∧ g.comp φ = ι.comp ψ := by
  first | exact @GlobalTheory.TraitLift.exists_ringHom_lift_of_isEtaleCompletion | exact GlobalTheory.TraitLift.exists_ringHom_lift_of_isEtaleCompletion | (intros; apply GlobalTheory.TraitLift.exists_ringHom_lift_of_isEtaleCompletion <;> assumption)
