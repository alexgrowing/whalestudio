import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLieBase
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsVarietyFlagRefinementBundleOfGoodModel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFlagRefinementBundleComp
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EigenFrameBasePointLiftsUniqueFlagSpace
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsIsoOfBijectiveGeomPointsSmoothProjCharZeroStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagSpaceComponentClassifyingMapBijectiveGeomPoiStatement
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical

namespace GlobalTheory.FlagCptRad

theorem isHom_apply_eq {F Ω Ω' : Type} [Field F] [Field Ω] [Algebra F Ω] [Field Ω'] [Algebra F Ω']
    {M : GlobalTheory.ZH.RatModel F Ω} {M' : GlobalTheory.ZH.RatModel F Ω'} {φ ψ : Ω →ₐ[F] Ω'} {f : M'.Z ⟶ M.Z}
    (hφ : M.IsHom M' φ f) (hψ : M.IsHom M' ψ f) (x : Ω) : φ x = ψ x := by
  have hx : ∀ w, x ∈ M.O (f (M'.pt w)) := fun w => by
    have e1 : (M'.pt ≫ f) w = f (M'.pt w) := Scheme.Hom.comp_apply _ _ _
    have e2 : (M'.pt ≫ f) w = genericPoint M.Z := by
      rw [hφ, Scheme.Hom.comp_apply, M.pt_apply]
    rw [← e1, e2, M.O_genericPoint]; exact Algebra.mem_top
  have h1 := hφ.val_comp M'.pt (IsLocalRing.closedPoint Ω') (hx _)
  have h2 := hψ.val_comp M'.pt (IsLocalRing.closedPoint Ω') (hx _)
  rw [GlobalTheory.ZH.RatModel.val_pt] at h1 h2
  exact h1.symm.trans h2

theorem keepsRad_of_flagCpt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (F : Type) [Field F] (e : F ≃+* c.F) (C : FlagCpt Z e) (X : Var F) (j : X.X ⟶ gen Z), IsOpenImmersion j → j ≫ genStr Z ≫ spMap e.toRingHom = X.str → ∀ (f : C.Y.X ⟶ X.X), f ≫ j = C.π → ∀ (f₀ : EigFrame Z (constF e X) (genericPt X ≫ j ≫ genι Z)) (Eb : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn), Tied e X j f₀ Eb A₀ → (∀ (K : Type) [Field K] [IsAlgClosed K] (χ : c.F →+* K) (x : Sp K ⟶ X.X), x ≫ j ≫ genStr Z = spMap χ → ∀ g : EigFrame Z χ (x ≫ j ≫ genι Z), ∃! p : Sp K ⟶ C.Y.X, p ≫ f = x ∧ C.Carries p g) → ∀ (φ : X.Fn →ₐ[F] C.Y.Fn), (ratOf X).IsHom (ratOf C.Y) φ f → KeepsRad (ratOf X) (ratOf C.Y) φ f := by
  intro E _ _ _ H Dw l Xo c O _ β Z F _ e C X j hj hjs f hf f₀ Eb A₀ hT hlift φ hφ
  haveI : CharZero F := RingHom.charZero e.toRingHom
  obtain ⟨Y', φ', f', S', -, hR⟩ := tower _ (ratOf X) X.dim Eb (good_ratOf X) (fun _ => Nat.zero_le _) rfl
  change Y'.X ⟶ X.X at f'
  obtain ⟨h, hh, hbij⟩ := GlobalTheory.T.flagSpaceComponent_classifyingMap_bijective_geomPoints E H Dw l Xo c O β Z F e C X j hj hjs f hf f₀ Eb A₀ hT hlift Y' φ' f' S' hR
  have hs' : f' ≫ X.str = Y'.str := hR.hom.inducedModelMorphism_comp_structureMap
  have hstr : h ≫ Y'.str = C.Y.str := by
    rw [← hs', ← Category.assoc, hh, ← hjs, ← C.π_str, ← hf, Category.assoc]
  have hiso : IsIso h := GlobalTheory.T.isIso_of_bijective_geomPoints_smoothProj_charZero F C.Y Y' h hstr hbij
  obtain ⟨ψ, S'', hR2⟩ := exists_refines_of_iso (ratOf Y') (ratOf C.Y) (@asIso _ _ _ _ h hiso) hstr S'
  have hR2' : Refines S' S'' ψ h := hR2
  subst hh
  have hR3 := hR.comp hR2'
  have hrad : KeepsRad (ratOf X) (ratOf C.Y) (ψ.comp φ') (h ≫ f') := hR3.rad
  have hhom : (ratOf X).IsHom (ratOf C.Y) (ψ.comp φ') (h ≫ f') := hR3.hom
  intro z' g hg
  rw [isHom_apply_eq hφ hhom g]
  exact hrad z' g hg

end GlobalTheory.FlagCptRad
