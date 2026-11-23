import Development.AbelianVarietyTheory.Definitions.Divisors.FormalEnd
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DvdOfForallHeightOneExistsDvdMul
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExpansionOfIntegralSectionIsIntegral
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.LocalInj

theorem base_to_stalk_injective : ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'], AdmBase R' (maximalIdeal R') → ∀ (G₁ : Over (Sp R')) [GrpObj G₁] [IsCommMonObj G₁], IsSemiAbelian G₁ → ∀ x : G₁.left, Function.Injective ((G₁.left.presheaf.germ ⊤ x trivial).hom.comp ((G₁.hom.appTop).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R')).inv.hom)) := by
  intro R' _ _ _ _ G₁ _ _ hG x
  haveI : Smooth G₁.hom := hG.smooth
  haveI : Flat G₁.hom := inferInstance

  have hst : Function.Injective (G₁.hom.stalkMap x).hom := by
    have h := Flat.stalkMap G₁.hom x
    letI := (G₁.hom.stalkMap x).hom.toAlgebra
    haveI : Module.Flat ((Sp R').presheaf.stalk (G₁.hom x)) (G₁.left.presheaf.stalk x) := h
    have : IsLocalHom (algebraMap ((Sp R').presheaf.stalk (G₁.hom x)) (G₁.left.presheaf.stalk x)) :=
      inferInstanceAs (IsLocalHom (G₁.hom.stalkMap x).hom)
    have := Module.FaithfullyFlat.of_flat_of_isLocalHom (A := (Sp R').presheaf.stalk (G₁.hom x))
      (B := G₁.left.presheaf.stalk x)
    exact FaithfulSMul.algebraMap_injective ((Sp R').presheaf.stalk (G₁.hom x)) (G₁.left.presheaf.stalk x)

  have hgerm : Function.Injective ((Sp R').presheaf.germ ⊤ (G₁.hom x) trivial).hom := by
    have hU := isAffineOpen_top (Sp R')
    let _ := (Sp R').presheaf.algebra_section_stalk (U := ⊤) ⟨G₁.hom x, trivial⟩
    have := hU.isLocalization_stalk ⟨G₁.hom x, trivial⟩
    haveI : IsDomain Γ(Sp R', ⊤) :=
      (Scheme.ΓSpecIso (CommRingCat.of R')).commRingCatIsoToRingEquiv.toMulEquiv.isDomain_iff.mpr inferInstance
    exact IsLocalization.injective (M := (hU.primeIdealOf ⟨G₁.hom x, trivial⟩).asIdeal.primeCompl)
      (S := (Sp R').presheaf.stalk ((⟨G₁.hom x, trivial⟩ : (⊤ : (Sp R').Opens)) : Sp R'))
      (Ideal.primeCompl_le_nonZeroDivisors _)
  have hiso : Function.Injective (Scheme.ΓSpecIso (CommRingCat.of R')).inv.hom :=
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R')).inv).1
  have e : ⇑((G₁.left.presheaf.germ ⊤ x trivial).hom.comp ((G₁.hom.appTop).hom.comp
      (Scheme.ΓSpecIso (CommRingCat.of R')).inv.hom)) =
      ⇑(G₁.hom.stalkMap x).hom ∘ ⇑((Sp R').presheaf.germ ⊤ (G₁.hom x) trivial).hom ∘
        ⇑(Scheme.ΓSpecIso (CommRingCat.of R')).inv.hom := by
    funext a
    exact (Scheme.Hom.germ_stalkMap_apply G₁.hom ⊤ x trivial _).symm
  rw [e]
  exact hst.comp (hgerm.comp hiso)

end GlobalTheory.Mum.LocalInj
