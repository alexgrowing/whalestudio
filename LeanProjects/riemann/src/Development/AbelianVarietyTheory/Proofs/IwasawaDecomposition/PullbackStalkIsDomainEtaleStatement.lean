import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PullbackStalkIsDomainEtale
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InRealConeSelf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PhiDivisorArcBlowup
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMonomialLevelFormDvr
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pullback_stalk_isDomain_etale : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (X Z : GMod Xo c) (Y : Model Xo c (RingHom.id c.F)) (π : Z.X ⟶ X.X) (e : gen Y ≅ gen Z) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (ξ : Sp R ⟶ X.X), IsEtaleCompletion (Scheme.stalkClosedPointTo ξ).hom → ∀ v : ↥(pullback ξ (e.hom ≫ genι Z ≫ π) : Scheme.{0}), IsDomain ((pullback ξ (e.hom ≫ genι Z ≫ π)).presheaf.stalk v) → ∀ (W : Type) [CommRing W] [IsDomain W] (g : (pullback ξ (e.hom ≫ genι Z ≫ π)).presheaf.stalk v →+* W), Function.Injective g → Set.range (jK W ≫ spMap g ≫ (pullback ξ (e.hom ≫ genι Z ≫ π)).fromSpecStalk v ≫ pullback.snd ξ (e.hom ≫ genι Z ≫ π) ≫ genι Y) ⊆ Set.range Y.j := by
  first | exact @GlobalTheory.TraitGeneric.range_generic_subset_range_j | exact GlobalTheory.TraitGeneric.range_generic_subset_range_j | (intros; apply GlobalTheory.TraitGeneric.range_generic_subset_range_j <;> assumption)
