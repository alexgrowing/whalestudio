import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InRealConeSelf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEtaleOfIsEtaleCompletion
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StalksOfRingStatementCharZero
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

namespace GlobalTheory.MixedLower

theorem stalk_pullback_normal_noetherian : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (X Z : GMod Xo c) (Y : Model Xo c (RingHom.id c.F)) (π : Z.X ⟶ X.X) (e : gen Y ≅ gen Z), Z.j ≫ π = X.j → π ≫ X.s = Z.s → Y.jQ ≫ e.hom = Z.jQ → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (ξ : Sp R ⟶ X.X), IsCN R → IsEtaleCompletion (Scheme.stalkClosedPointTo ξ).hom → ((residue R).comp (Scheme.stalkClosedPointTo ξ).hom).FormallyUnramified → ∀ v : ↥(pullback ξ (e.hom ≫ genι Z ≫ π) : Scheme.{0}), IsDomain ((pullback ξ (e.hom ≫ genι Z ≫ π)).presheaf.stalk v) ∧ IsIntegrallyClosed ((pullback ξ (e.hom ≫ genι Z ≫ π)).presheaf.stalk v) ∧ IsNoetherianRing ((pullback ξ (e.hom ≫ genι Z ≫ π)).presheaf.stalk v) :=
  GlobalTheory.NormalBaseChange.stalks_of_ring_statement_charZero GlobalTheory.NormalBaseChange.normal_noetherian_tensor

end GlobalTheory.MixedLower
