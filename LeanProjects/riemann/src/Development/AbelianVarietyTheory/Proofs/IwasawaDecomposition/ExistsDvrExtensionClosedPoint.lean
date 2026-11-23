import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartMem
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHenselRootResidueStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolynomialApproxPowMaximalStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolynomialApproxUniquenessStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HenselRootsCompatibleStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPrimitiveElementUnramifiedStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCommonUnramifiedExtensionStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsDvrResidueLiftIrreducibleStatement
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

noncomputable section

namespace GlobalTheory.TraitLift

theorem eq_of_stalkClosedPointTo' {X : Scheme.{0}} {R W V : Type} [CommRing R] [IsLocalRing R] [CommRing W]
    [IsLocalRing W] [CommRing V] [IsLocalRing V] (ξ : Sp R ⟶ X) (χ : Sp W ⟶ X) (h : ξ (closedPoint R) = χ (closedPoint W))
    (ψ : R →+* V) (f : W →+* V)
    (hc : ψ.comp (Scheme.stalkClosedPointTo ξ).hom =
      f.comp ((X.presheaf.stalkCongr (Inseparable.of_eq h)).hom ≫ Scheme.stalkClosedPointTo χ).hom) :
    spMap f ≫ χ = spMap ψ ≫ ξ := by
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

theorem exists_lift : ∀ (X : Scheme.{0}) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (ξ : Sp R ⟶ X), IsCN R → IsEtaleCompletion (Scheme.stalkClosedPointTo ξ).hom → ((residue R).comp (Scheme.stalkClosedPointTo ξ).hom).FormallyUnramified → ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], CDvr W → ∀ ϖ : W, Irreducible ϖ → ∀ (χ : Sp W ⟶ X), χ (closedPoint W) = ξ (closedPoint R) → ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsLocalRing V) (f : W →+* V) (ψ : R →+* V), CDvr V ∧ Function.Injective f ∧ IsLocalHom f ∧ IsLocalHom ψ ∧ Irreducible (f ϖ) ∧ spMap f ≫ χ = spMap ψ ≫ ξ := by
  intro X R _ _ _ ξ hR hξ hur W _ _ _ hW ϖ hϖ χ hχ
  obtain ⟨-, -, hRc, -⟩ := hR
  haveI := hRc
  have hpt : ξ (closedPoint R) = χ (closedPoint W) := hχ.symm
  let φ : X.presheaf.stalk (ξ (closedPoint R)) →+* R := (Scheme.stalkClosedPointTo ξ).hom
  let α : X.presheaf.stalk (ξ (closedPoint R)) →+* W :=
    ((X.presheaf.stalkCongr (Inseparable.of_eq hpt)).hom ≫ Scheme.stalkClosedPointTo χ).hom
  haveI : IsLocalHom α := by
    simp only [α, CommRingCat.hom_comp]
    infer_instance
  haveI : IsLocalHom φ := Scheme.isLocalHom_stalkClosedPointTo' ξ
  obtain ⟨hflat, hmax, hfin⟩ := hξ
  have hfin' : (ResidueField.map φ).Finite := by
    rw [← ResidueField.map_comp_residue] at hfin
    exact RingHom.Finite.of_comp_finite hfin
  have hur' : (ResidueField.map φ).FormallyUnramified := by
    rw [← ResidueField.map_comp_residue] at hur
    exact RingHom.FormallyUnramified.of_comp hur
  obtain ⟨θ, q, hqm, hqθ, hqd, hgen, hind⟩ := GlobalTheory.T.exists_primitive_element_unramified φ hfin hur
  obtain ⟨M, _, u, v, huv, hvf, hvu⟩ := GlobalTheory.T.exists_common_unramified_extension (ResidueField.map φ) (ResidueField.map α) hfin' hur'
  obtain ⟨V, _, _, _, f, τ, hV, hfinj, hfloc, hirr, hτ⟩ := GlobalTheory.T.exists_dvr_residue_lift_irreducible W hW v hvf hvu
  haveI := hV.2.1
  let σ : ResidueField R →+* ResidueField V := τ.comp u
  have hσ : ∀ a, σ (residue R (φ a)) = residue V ((f.comp α) a) := by
    intro a
    have h1 := congrArg (fun g => g (residue _ a)) huv
    simp only [RingHom.comp_apply, ResidueField.map_residue] at h1
    simp only [σ, RingHom.comp_apply, h1, hτ]
  obtain ⟨η, hη, -⟩ := GlobalTheory.T.exists_hensel_root_residue φ (f.comp α) σ hσ θ q hqm hqθ hqd
  have hgp := GlobalTheory.T.polynomial_approx_pow_maximal φ hmax θ hgen
  have hip := GlobalTheory.T.polynomial_approx_uniqueness φ hflat hmax θ q hqm hqθ hgp hind
  obtain ⟨ψ, hψ, hψl⟩ := GlobalTheory.T.hensel_roots_compatible φ (f.comp α) inferInstance θ η q hqm hqθ hη hgp hip
  exact ⟨V, inferInstance, inferInstance, inferInstance, f, ψ, hV, hfinj, hfloc, hψl, hirr ϖ hϖ,
    eq_of_stalkClosedPointTo' ξ χ hpt ψ f hψ⟩

end GlobalTheory.TraitLift
