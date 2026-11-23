import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TrvEqSelf
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

namespace GlobalTheory.FixStalk

theorem fixes_stalk : ∀ (X : Scheme.{0}) [IsIntegral X] (b : X ≅ X) (x : X), X.fromSpecResidueField x ≫ b.hom = X.fromSpecResidueField x → ∃ st : X.presheaf.stalk x →+* X.presheaf.stalk x, (show Sp (X.presheaf.stalk x) ⟶ X from X.fromSpecStalk x) ≫ b.hom = spMap st ≫ X.fromSpecStalk x ∧ (∀ a, IsLocalRing.residue (X.presheaf.stalk x) (st a) = IsLocalRing.residue (X.presheaf.stalk x) a) ∧ ∀ a, GlobalTheory.functionFieldMap b.hom (algebraMap (X.presheaf.stalk x) X.functionField a) = algebraMap (X.presheaf.stalk x) X.functionField (st a) := by
  intro X _ b x hb
  have hx : b.hom x = x := by
    obtain ⟨p⟩ : Nonempty ↥(Spec (X.residueField x)) := ⟨IsLocalRing.closedPoint _⟩
    have h2 := Scheme.fromSpecResidueField_apply x p
    have h3 : b.hom (X.fromSpecResidueField x p) = X.fromSpecResidueField x p := by
      rw [← Scheme.Hom.comp_apply, hb]
    rwa [h2] at h3
  have hs : b.hom x ⤳ x := by rw [hx]
  have hs' : x ⤳ b.hom x := by rw [hx]
  let st : X.presheaf.stalk x ⟶ X.presheaf.stalk x :=
    X.presheaf.stalkSpecializes hs ≫ b.hom.stalkMap x
  have h0 : X.fromSpecStalk x ≫ b.hom = Spec.map st ≫ X.fromSpecStalk x := by
    rw [Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk,
      Scheme.SpecMap_stalkMap_fromSpecStalk]
  have h1 : (show Sp (X.presheaf.stalk x) ⟶ X from X.fromSpecStalk x) ≫ b.hom =
      spMap st.hom ≫ X.fromSpecStalk x := by
    simpa only [spMap, CommRingCat.ofHom_hom] using h0
  haveI : IsIso (X.presheaf.stalkSpecializes hs) :=
    ⟨⟨X.presheaf.stalkSpecializes hs', by simp, by simp⟩⟩
  haveI : IsLocalHom st.hom := by
    show IsLocalHom (X.presheaf.stalkSpecializes hs ≫ b.hom.stalkMap x).hom
    rw [CommRingCat.hom_comp]
    infer_instance
  haveI : IsLocalHom (X.residue x).hom := inferInstanceAs (IsLocalHom (IsLocalRing.residue _))
  haveI : IsLocalHom (st ≫ X.residue x).hom := by
    rw [CommRingCat.hom_comp]
    infer_instance
  refine ⟨st.hom, h1, ?_, ?_⟩
  · have e : Spec.map (X.residue x) ≫ X.fromSpecStalk x =
        Spec.map (st ≫ X.residue x) ≫ X.fromSpecStalk x := by
      rw [Spec.map_comp, Category.assoc, ← h0, ← Category.assoc]
      exact hb.symm
    have e2 := (SpecToEquivOfLocalRing X (X.residueField x)).symm.injective
      (a₁ := ⟨x, ⟨X.residue x, inferInstance⟩⟩) (a₂ := ⟨x, ⟨st ≫ X.residue x, inferInstance⟩⟩) e
    obtain ⟨_, e3⟩ := SpecToEquivOfLocalRing_eq_iff.mp e2
    simp only [TopCat.Presheaf.stalkCongr_hom, TopCat.Presheaf.stalkSpecializes_refl,
      Category.id_comp] at e3
    intro a
    exact (congr($e3 a)).symm
  · intro a
    have e4 : algebraMap (X.presheaf.stalk x) X.functionField a =
        algebraMap (X.presheaf.stalk (b.hom x)) X.functionField (X.presheaf.stalkSpecializes hs a) := by
      simp only [RingHom.algebraMap_toAlgebra]
      rw [← CommRingCat.comp_apply, TopCat.Presheaf.stalkSpecializes_comp]
    rw [e4, GlobalTheory.functionFieldMap_algebraMap]
    rfl

end GlobalTheory.FixStalk
