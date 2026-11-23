import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PowIdeal
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.RelSerreSections
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.QcqsPushforward

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh TensorProduct
open TopologicalSpace Opposite

namespace GlobalTheory.CompanionTheory.GE.PushCoh

abbrev overAffine {X Z : Scheme.{0}} (φ : Z ⟶ X) {V : X.Opens} (hV : IsAffineOpen V) :
    (φ ⁻¹ᵁ V).toScheme.Over (Spec (.of Γ(X, V))) :=
  ⟨φ ∣_ V ≫ hV.isoSpec.hom⟩

attribute [local instance] algebraOfOver

lemma algebraMap_overAffine {X Z : Scheme.{0}} (φ : Z ⟶ X) {V : X.Opens} (hV : IsAffineOpen V)
    (b : Γ(X, V)) :
    letI := overAffine φ hV
    Z.presheaf.map (eqToHom (Scheme.Opens.ι_image_top (φ ⁻¹ᵁ V)).symm).op
      (algebraMap Γ(X, V) Γ((φ ⁻¹ᵁ V).toScheme, ⊤) b : Γ(Z, (φ ⁻¹ᵁ V).ι ''ᵁ ⊤)) =
      φ.app V b := by
  letI := overAffine φ hV
  have s1 : algebraMap Γ(X, V) Γ((φ ⁻¹ᵁ V).toScheme, ⊤) b = (φ ∣_ V).appTop (V.topIso.inv b) := by
    change (φ ∣_ V ≫ hV.isoSpec.hom).appTop ((Scheme.ΓSpecIso (.of Γ(X, V))).inv b) = _
    rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, IsAffineOpen.isoSpec_hom_appTop,
      CommRingCat.comp_apply]
    erw [Iso.inv_hom_id_apply]
  rw [s1]
  erw [morphismRestrict_appTop, Scheme.Opens.topIso_inv, CommRingCat.comp_apply]
  refine (RelSerre.app_eqToHom_apply φ (Scheme.Opens.ι_image_top V) _ _ b).trans ?_
  simp

def zerothCohomologyToSections {X Z : Scheme.{0}} (φ : Z ⟶ X) {V : X.Opens} (hV : IsAffineOpen V) (M : Z.Modules) :
    letI := overAffine φ hV
    Sheaf.H.{0} (modulesAb (M.restrict (φ ⁻¹ᵁ V).ι)) 0 →ₗ[Γ(X, V)]
      Γ((Scheme.Modules.pushforward φ).obj M, V) :=
  letI := overAffine φ hV
  { toFun := fun x => M.presheaf.map (eqToHom (Scheme.Opens.ι_image_top (φ ⁻¹ᵁ V)).symm).op
      (Sheaf.H.equiv₀ (modulesAb (M.restrict (φ ⁻¹ᵁ V).ι)) isTerminalTop x :
        Γ(M, (φ ⁻¹ᵁ V).ι ''ᵁ ⊤))
    map_add' := fun x y => by
      rw [map_add]
      exact map_add _ _ _
    map_smul' := fun b x => by
      rw [H.smul_def, ← Sheaf.H.equiv₀_naturality]
      refine (RelSerre.smul_restrict_top M (φ ⁻¹ᵁ V) _ _).trans ?_
      refine (congrArg (· • _) (algebraMap_overAffine φ hV b)).trans ?_
      exact (smul_pushforward φ M b _).symm }

lemma zeroth_cohomology_to_sections_surjective {X Z : Scheme.{0}} (φ : Z ⟶ X) {V : X.Opens} (hV : IsAffineOpen V)
    (M : Z.Modules) : Function.Surjective (zerothCohomologyToSections φ hV M) := by
  letI := overAffine φ hV
  exact ((ConcreteCategory.bijective_of_isIso (M.presheaf.map
    (eqToHom (Scheme.Opens.ι_image_top (φ ⁻¹ᵁ V)).symm).op)).comp
    (Sheaf.H.equiv₀ (modulesAb (M.restrict (φ ⁻¹ᵁ V).ι)) isTerminalTop).bijective).2

theorem isCoherent_pushforward_of_isProper {X Z : Scheme.{0}} [IsLocallyNoetherian X] (φ : Z ⟶ X)
    (hφ : IsProper φ) {G : Z.Modules} (hG : IsCoherent G) :
    IsCoherent ((Scheme.Modules.pushforward φ).obj G) := by
  haveI := hG.1
  refine ⟨isQuasicoherent_pushforward_of_qcqs φ G, fun V hV => ?_⟩
  letI := overAffine φ hV
  haveI : IsNoetherianRing Γ(X, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  haveI : IsProper ((φ ⁻¹ᵁ V).toScheme ↘ Spec (.of Γ(X, V))) := by
    change IsProper (φ ∣_ V ≫ hV.isoSpec.hom)
    infer_instance
  have hfin := finite_H_of_isProper (A := Γ(X, V)) (G.restrict (φ ⁻¹ᵁ V).ι) (hG.restrict _) 0
  exact Module.Finite.of_surjective (zerothCohomologyToSections φ hV G) (zeroth_cohomology_to_sections_surjective φ hV G)

end GlobalTheory.CompanionTheory.GE.PushCoh

end
