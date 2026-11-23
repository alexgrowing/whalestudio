import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompleteUnramifiedResidueLift
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSiegPull
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.SiegLoc GlobalTheory
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.complete_unramified_residue_lift : ∀ (S₀ B R₀ k' : Type) [CommRing S₀] [IsLocalRing S₀] [CommRing B] [IsDomain B] [IsLocalRing B] [IsIntegrallyClosed B] [CharZero B] [Algebra.EssFiniteType ℤ B] [CommRing R₀] [IsLocalRing R₀] [Field k'] (f : S₀ →+* B) (g : S₀ →+* R₀) (v : ResidueField B →+* k'), IsAdicComplete (maximalIdeal R₀) R₀ → IsLocalHom f → IsLocalHom g → IsEtaleCompletion g → ((residue R₀).comp g).FormallyUnramified → v.Finite → v.FormallyUnramified → ∃ (A : Type) (_ : CommRing A) (_ : IsDomain A) (_ : IsLocalRing A) (ψ : B →+* A) (φ : R₀ →+* A) (τ : k' →+* ResidueField A), IsCN A ∧ IsLocalHom ψ ∧ IsEtaleCompletion ψ ∧ ((residue A).comp ψ).FormallyUnramified ∧ IsLocalHom φ ∧ ψ.comp f = φ.comp g ∧ τ.comp (v.comp (residue B)) = (residue A).comp ψ := by
  first | exact @GlobalTheory.EtaleCompletionLift.exists_etaleCompletion_over | exact GlobalTheory.EtaleCompletionLift.exists_etaleCompletion_over | (intros; apply GlobalTheory.EtaleCompletionLift.exists_etaleCompletion_over <;> assumption)
