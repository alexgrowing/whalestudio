import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyFilteredColimitRingsFinitaryStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

noncomputable section
namespace GlobalTheory.EtC

abbrev isoSpecSp (X : Scheme.{0}) [IsAffine X] : sch.obj X ⟶ sp Γ(X, ⊤) := sch.map X.isoSpec.hom

theorem pull_isoSpecSp_inv (R : Type) [CommRing R] (F : Shv R) (n : ℤ) (X : Scheme.{0}) [IsAffine X]
    (x : H R (sch.obj X) F n) : pull R (isoSpecSp X) F n (pull R (sch.map X.isoSpec.inv) F n x) = x := by
  rw [← pull_comp, ← sch.map_comp, Iso.hom_inv_id, sch.map_id, pull_id]

theorem pull_isoSpecSp_inv' (R : Type) [CommRing R] (F : Shv R) (n : ℤ) (X : Scheme.{0}) [IsAffine X]
    (x : H R (sp Γ(X, ⊤)) F n) : pull R (sch.map X.isoSpec.inv) F n (pull R (isoSpecSp X) F n x) = x := by
  rw [← pull_comp, ← sch.map_comp, Iso.inv_hom_id, sch.map_id, pull_id]

theorem isoSpecSp_naturality {X Y : Scheme.{0}} [IsAffine X] [IsAffine Y] (f : X ⟶ Y) :
    isoSpecSp X ≫ spMap f.appTop.hom = sch.map f ≫ isoSpecSp Y := by
  simp only [isoSpecSp, spMap, CommRingCat.ofHom_hom, ← sch.map_comp, Scheme.isoSpec_hom_naturality]

theorem pull_isoSpecSp_naturality (R : Type) [CommRing R] (F : Shv R) (n : ℤ) {X Y : Scheme.{0}} [IsAffine X] [IsAffine Y]
    (f : X ⟶ Y) (z : H R (sp Γ(Y, ⊤)) F n) :
    pull R (sch.map f) F n (pull R (isoSpecSp Y) F n z) = pull R (isoSpecSp X) F n (pull R (spMap f.appTop.hom) F n z) := by
  rw [← pull_comp, ← pull_comp, isoSpecSp_naturality]

theorem contCone_of_affine_limit : ∀ (R : Type) [CommRing R] (F : Shv R), Finitary F → ∀ (I : Type) [SmallCategory I] [IsCofiltered I] (G : I ⥤ Scheme.{0}) (c : Cone G), IsLimit c → (∀ i, IsAffine (G.obj i)) → ContCone R F (sch.mapCone c) := by
  intro R _ F hF I _ _ G c hc hG
  haveI : IsAffine c.pt := Scheme.isAffine_of_isLimit c hc
  let c' : Cocone (G ⋙ Scheme.Γ.rightOp).leftOp := coconeLeftOpOfCone (Scheme.Γ.rightOp.mapCone c)
  have hc' : IsColimit c' := isColimitCoconeLeftOpOfCone _ (isLimitOfPreserves Scheme.Γ.rightOp hc)
  have hb := GlobalTheory.T.etaleCohomology_filteredColimit_rings_finitary R F hF Iᵒᵖ _ c' hc'
  intro n
  obtain ⟨h1, h2⟩ := hb n
  refine ⟨fun x => ?_, fun i y hy => ?_⟩
  · obtain ⟨j, y', hy'⟩ := h1 (pull R (sch.map c.pt.isoSpec.inv) F n x)
    refine ⟨j.unop, pull R (isoSpecSp (G.obj j.unop)) F n y', ?_⟩
    change pull R (sch.map (c.π.app j.unop)) F n _ = x
    refine (pull_isoSpecSp_naturality R F n (X := c.pt) (Y := G.obj j.unop) (c.π.app j.unop) y').trans ?_
    change pull R (isoSpecSp c.pt) F n (pull R (spMap (c'.ι.app j).hom) F n y') = x
    rw [hy', pull_isoSpecSp_inv]
  · change pull R (sch.map (c.π.app i)) F n y = 0 at hy
    let y' : H R (sp Γ(G.obj i, ⊤)) F n := pull R (sch.map (G.obj i).isoSpec.inv) F n y
    have hyy : y = pull R (isoSpecSp (G.obj i)) F n y' := (pull_isoSpecSp_inv R F n _ y).symm
    have hz : pull R (spMap (c'.ι.app (op i)).hom) F n y' = 0 := by
      have e : pull R (isoSpecSp c.pt) F n (pull R (spMap (c.π.app i).appTop.hom) F n y') = 0 := by
        rw [← pull_isoSpecSp_naturality R F n (X := c.pt) (Y := G.obj i) (c.π.app i) y', ← hyy]
        exact hy
      have e2 := congrArg (pull R (sch.map c.pt.isoSpec.inv) F n) e
      rw [pull_isoSpecSp_inv', map_zero] at e2
      exact e2
    obtain ⟨k, f, hk⟩ := h2 (op i) y' hz
    refine ⟨k.unop, f.unop, ?_⟩
    change pull R (sch.map (G.map f.unop)) F n y = 0
    rw [hyy]
    refine (pull_isoSpecSp_naturality R F n (X := G.obj k.unop) (Y := G.obj i) (G.map f.unop) y').trans ?_
    change pull R (isoSpecSp (G.obj k.unop)) F n (pull R (spMap ((G ⋙ Scheme.Γ.rightOp).leftOp.map f).hom) F n y') = 0
    rw [hk]
    exact AddMonoidHom.map_zero _

end GlobalTheory.EtC
end
