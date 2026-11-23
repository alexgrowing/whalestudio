import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GrothendieckDeformation
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JetGroupMorphismBaseChangeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JetMorphismAdmissibleConnectionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JetMorphismDeterminantGeneratorStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.LatVal GlobalTheory.LatJet

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LatJet

theorem jetConstMor {F : Type} [Field F] [NumberField F] {𝔠 : FracId F} {R : Type} [CommRing R] {I : Type}
    [Fintype I] {n : ℕ} (J : JetRing R I n) (X : Obj F 𝔠 (Sp R)) :
    GrpMor (dp0 R) (𝟙 _) X.A J.κ (spMap J.π) X.A (algebraMap R J.B) (𝟙 _) (Over.Hom.left (𝟙 X.A)) := by
  have e : J.π.comp (algebraMap R J.B) = RingHom.id R := by
    ext r
    simp only [RingHom.comp_apply, RingHom.id_apply, J.π_eq, Algebra.algebraMap_eq_smul_one, ← J.one, map_smul,
      Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_eq_same, smul_eq_mul]
    exact mul_one r
  refine GrpMor.of_hom (isDPMorphism_of_eq_bot _ rfl _ _) ?_ (𝟙 X.A)
  rw [← Cris.spMap_comp, e, Cris.spMap_id]

theorem jetLift_of_deformation_of_deRham (hGD : GlobalTheory.Published.GrothendieckDeformation) (hDR : GlobalTheory.Published.AbelianDeRham)
    (hDC : GlobalTheory.Published.AbelianDualCrystal) : JetLift := by
  intro F _ _ _ 𝔠 R _ _ _ _ I _ n J X δ N hN
  have m := jetConstMor J X
  obtain ⟨X', i, pull, hF⟩ := GlobalTheory.T.jet_morphism_admissible_connection hGD hDR hDC F 𝔠 R I n J X N hN m
  obtain ⟨δ', hδ⟩ := GlobalTheory.T.jet_morphism_determinant_generator hGD hDR hDC F 𝔠 R I n J X δ N hN m
    (GlobalTheory.T.jet_group_morphism_base_change hGD hDR hDC F 𝔠 R I n J X m) X' i pull hF
  exact ⟨⟨X', i, pull, m, δ', fun x hx d hd ↦ hF ▸ Submodule.subset_span ⟨x, hx, hd⟩, hδ⟩⟩

end GlobalTheory.LatJet
