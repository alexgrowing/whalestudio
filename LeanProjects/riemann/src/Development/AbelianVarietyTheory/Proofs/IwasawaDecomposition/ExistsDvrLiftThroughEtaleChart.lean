import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasConesIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolynomialSupportHolds
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolarizationTransferModels
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.MvPowerSeriesSubstConstTermsLocalAlgHomSpec
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsDvrResidueExtensionStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPrimitiveElementCompleteStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHenselRootResidueStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolynomialApproxPowMaximalStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolynomialApproxUniquenessStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HenselRootsCompatibleStatement
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

noncomputable section

namespace GlobalTheory.ChartLift

theorem eq_of_stalkClosedPointTo : ∀ {X : Scheme.{0}} {R W V : Type} [CommRing R] [IsLocalRing R] [CommRing W] [IsLocalRing W] [CommRing V] [IsLocalRing V] (ξ : Sp R ⟶ X) (χ : Sp W ⟶ X) (h : ξ (closedPoint R) = χ (closedPoint W)) (ψ : R →+* V) (f : W →+* V), IsLocalHom ψ → IsLocalHom f → ψ.comp (Scheme.stalkClosedPointTo ξ).hom = f.comp ((X.presheaf.stalkCongr (Inseparable.of_eq h)).hom ≫ Scheme.stalkClosedPointTo χ).hom → spMap f ≫ χ = spMap ψ ≫ ξ := by
  intro X R W V _ _ _ _ _ _ ξ χ h ψ f hψ hf hc
  have key : ∀ (x y : X) (hxy : x = y) (g : X.presheaf.stalk y ⟶ CommRingCat.of V),
      Spec.map ((X.presheaf.stalkCongr (Inseparable.of_eq hxy)).hom ≫ g) ≫ X.fromSpecStalk x =
        Spec.map g ≫ X.fromSpecStalk y := by
    intro x y hxy g
    subst hxy
    simp
  have hc' : Scheme.stalkClosedPointTo ξ ≫ CommRingCat.ofHom ψ =
      (X.presheaf.stalkCongr (Inseparable.of_eq h)).hom ≫ Scheme.stalkClosedPointTo χ ≫ CommRingCat.ofHom f := by
    ext a
    exact congrArg (fun g : _ →+* V => g a) hc
  conv_lhs => rw [← Scheme.Spec_stalkClosedPointTo_fromSpecStalk χ]
  conv_rhs => rw [← Scheme.Spec_stalkClosedPointTo_fromSpecStalk ξ]
  simp only [spMap, ← Category.assoc, ← Spec.map_comp]
  rw [hc', key _ _ h]

theorem exists_lift_to_chart : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} (Y : Model Xo c (RingHom.id c.F)) {k : Type} [Field k] {m e : ℕ} (ξ : Sp (ChartRing k m e) ⟶ gen Y), IsEtaleCompletion (Scheme.stalkClosedPointTo ξ).hom → ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], CDvr W → ∀ (χ : Sp W ⟶ Y.X), χ (closedPoint W) = genι Y (ξ (closedPoint _)) → ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsLocalRing V) (f : W →+* V) (ψ : ChartRing k m e →+* V), CDvr V ∧ Function.Injective f ∧ IsLocalHom f ∧ IsLocalHom ψ ∧ spMap f ≫ χ = spMap ψ ≫ ξ ≫ genι Y := by
  intro E _ _ _ H D l Xo c Y k _ m e ξ hξ W _ _ _ hW χ hχ
  have hiso : IsIso (spMap (RingHom.id c.F)) := by
    show IsIso (Spec.map (CommRingCat.ofHom (RingHom.id c.F)))
    rw [show CommRingCat.ofHom (RingHom.id c.F) = 𝟙 (CommRingCat.of c.F) from rfl, Spec.map_id]
    infer_instance
  haveI : IsIso (genι Y) := inferInstance
  let χ' : Sp W ⟶ gen Y := χ ≫ inv (genι Y)
  have hχχ : χ' ≫ genι Y = χ := by simp [χ']
  have hpt : ξ (closedPoint (ChartRing k m e)) = χ' (closedPoint W) := by
    have h1 : genι Y (χ' (closedPoint W)) = χ (closedPoint W) := by
      rw [← hχχ]; rfl
    apply (genι Y).isOpenEmbedding.injective
    rw [h1, hχ]
  let φ : (gen Y).presheaf.stalk (ξ (closedPoint (ChartRing k m e))) →+* ChartRing k m e := (Scheme.stalkClosedPointTo ξ).hom
  let α : (gen Y).presheaf.stalk (ξ (closedPoint (ChartRing k m e))) →+* W := (((gen Y).presheaf.stalkCongr (Inseparable.of_eq hpt)).hom ≫ Scheme.stalkClosedPointTo χ').hom
  haveI : IsLocalHom α := by
    simp only [α, CommRingCat.hom_comp]
    infer_instance
  haveI : IsLocalHom φ := Scheme.isLocalHom_stalkClosedPointTo' ξ
  obtain ⟨hflat, hmax, hfin⟩ := hξ
  have hfin' : (ResidueField.map φ).Finite := by
    rw [← ResidueField.map_comp_residue] at hfin
    exact RingHom.Finite.of_comp_finite hfin
  have hch0 : CharZero (ResidueField ((gen Y).presheaf.stalk (ξ (closedPoint (ChartRing k m e))))) := by
    let g : c.F →+* ResidueField ((gen Y).presheaf.stalk (ξ (closedPoint (ChartRing k m e)))) :=
      (residue _).comp ((Scheme.ΓSpecIso (CommRingCat.of c.F)).inv ≫
        (Sp c.F).presheaf.germ ⊤ ((genStr Y) (ξ (closedPoint _))) trivial ≫
        (genStr Y).stalkMap (ξ (closedPoint _))).hom
    exact (RingHom.charZero_iff g.injective).1 inferInstance
  obtain ⟨V, _, _, _, f, hV, hfinj, hfloc, σ, hσ⟩ := GlobalTheory.T.exists_dvr_residue_extension (ResidueField.map φ) hfin' hch0 W hW α inferInstance
  haveI := hV.2.1
  have : IsAdicComplete (maximalIdeal k) k := by rw [maximalIdeal_eq_bot]; infer_instance
  haveI hCA : IsAdicComplete (maximalIdeal (ChartRing k m e)) (ChartRing k m e) :=
    GlobalTheory.PlaceInt.isAdicComplete_mvPowerSeries_finite (V := k) _
  obtain ⟨θ, q, hqm, hqθ, hqd, hgen, hind⟩ := GlobalTheory.T.exists_primitive_element_complete φ hfin' hch0
  obtain ⟨η, hη, -⟩ := GlobalTheory.T.exists_hensel_root_residue φ (f.comp α) σ (fun a => by rw [RingHom.comp_apply, ← hσ a, ResidueField.map_residue]) θ q hqm hqθ hqd
  have hgp := GlobalTheory.T.polynomial_approx_pow_maximal φ hmax θ hgen
  have hip := GlobalTheory.T.polynomial_approx_uniqueness φ hflat hmax θ q hqm hqθ hgp hind
  obtain ⟨ψ, hψ, hψl⟩ := GlobalTheory.T.hensel_roots_compatible φ (f.comp α) inferInstance θ η q hqm hqθ hη hgp hip
  refine ⟨V, inferInstance, inferInstance, inferInstance, f, ψ, hV, hfinj, hfloc, hψl, ?_⟩
  have hg := eq_of_stalkClosedPointTo ξ χ' hpt ψ f hψl hfloc hψ
  rw [← hχχ, ← Category.assoc, hg, Category.assoc]

end GlobalTheory.ChartLift
