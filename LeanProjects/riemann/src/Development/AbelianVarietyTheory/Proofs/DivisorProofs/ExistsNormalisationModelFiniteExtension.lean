import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LabRange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalModelNormalisationDedekind
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc

theorem RatModel.stalkMap_pt_surjective {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω)
    (y : Sp Ω) : Function.Surjective (M.pt.stalkMap y).hom := by
  obtain rfl : y = closedPoint Ω := Subsingleton.elim _ _
  intro t
  obtain ⟨U, f, hU, hf⟩ := M.onto ((stalkClosedPointIso (CommRingCat.of Ω)).hom.hom t)
  have h : ⊤ ≤ M.pt ⁻¹ᵁ U := M.top_le_preimage_pt hU
  have e := GlobalTheory.Points.germ_stalkClosedPointTo_eq_valMap M.pt U h
  refine ⟨(M.Z.presheaf.germ U _ ((GlobalTheory.Points.le_preimage_iff M.pt U).1 h)).hom f, ?_⟩
  apply (ConcreteCategory.bijective_of_isIso (stalkClosedPointIso (CommRingCat.of Ω)).hom).1
  have e2 := congrArg (fun φ => φ.hom f) e
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e2
  rw [GlobalTheory.Points.valF_eq_valR, GlobalTheory.Points.valR_eq _ _ h] at hf
  rw [← hf, ← e2]
  rfl

theorem stalkMap_spMap_finite {K L : Type} [Field K] [Field L] (φ : K →+* L) (hφ : φ.Finite) (y : Sp L) :
    ((spMap φ).stalkMap y).hom.Finite := by
  obtain rfl : y = closedPoint L := Subsingleton.elim _ _
  have e := Scheme.germ_stalkClosedPointTo_Spec (CommRingCat.ofHom φ)
  have hc : (Scheme.stalkClosedPointTo (spMap φ)).hom.Finite := by
    apply RingHom.Finite.of_comp_finite (f := ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫
      (Spec (CommRingCat.of K)).presheaf.germ ⊤ _ trivial).hom)
    have : ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫
      (Spec (CommRingCat.of K)).presheaf.germ ⊤ _ trivial ≫ Scheme.stalkClosedPointTo (spMap φ)) =
        CommRingCat.ofHom φ := by
      rw [e, Iso.inv_hom_id_assoc]
    rw [← CommRingCat.hom_comp, Category.assoc, this]
    exact hφ
  have : (spMap φ).stalkMap (closedPoint L) =
      Scheme.stalkClosedPointTo (spMap φ) ≫ (stalkClosedPointIso (CommRingCat.of L)).inv := by
    rw [Scheme.stalkClosedPointTo, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [this, CommRingCat.hom_comp]
  exact RingHom.Finite.comp (RingHom.Finite.of_surjective _
    (ConcreteCategory.bijective_of_isIso (stalkClosedPointIso (CommRingCat.of L)).inv).2) hc

end GlobalTheory.Poinc

namespace GlobalTheory.Poinc

theorem Setup.exists_model_of_finiteDimensional : ∀ {g n : ℕ} {F : SFam g n (zetaAway n)} {W : Matrix (Fin 8) (Fin 8) ℤ}
    {Z : Scheme.{0}} {i : F.X ⟶ Z} (X₁ : Setup F W i) (o₂ Ω₂ : Type) [CommRing o₂] [Field Ω₂] [Algebra o₂ Ω₂]
    [ArithBase o₂ Ω₂] [Algebra X₁.Ω₁ Ω₂] [FiniteDimensional X₁.Ω₁ Ω₂] (κ : X₁.o₁ →+* o₂), κ.Finite →
    (algebraMap o₂ Ω₂).comp κ = (algebraMap X₁.Ω₁ Ω₂).comp (algebraMap X₁.o₁ X₁.Ω₁) →
    ∃ (M : RatModel o₂ Ω₂) (q : M.Z ⟶ X₁.M.Z), GlobalTheory.IsNormalScheme M.Z ∧ IsFinite q ∧
      M.pt ≫ q = spMap (algebraMap X₁.Ω₁ Ω₂) ≫ X₁.M.pt := by
  intro g n F W Z i X₁ o₂ Ω₂ _ _ _ _ _ _ κ hκ hc
  haveI : IsDedekindDomain X₁.o₁ := ArithBase.ded (o := X₁.o₁) (Ω := X₁.Ω₁)
  have hp : (spMap (algebraMap X₁.Ω₁ Ω₂) ≫ X₁.M.pt) ≫ X₁.M.s = spMap ((algebraMap o₂ Ω₂).comp κ) := by
    rw [Category.assoc, X₁.M.pt_s, hc]
    exact (Spec.map_comp (CommRingCat.ofHom (algebraMap X₁.o₁ X₁.Ω₁))
      (CommRingCat.ofHom (algebraMap X₁.Ω₁ Ω₂))).symm
  have hst : ((spMap (algebraMap X₁.Ω₁ Ω₂) ≫ X₁.M.pt).stalkMap (genericPoint (Sp Ω₂))).hom.Finite := by
    rw [Scheme.Hom.stalkMap_comp]
    exact RingHom.Finite.comp (stalkMap_spMap_finite _ (RingHom.finite_algebraMap.2 inferInstance) _)
      (RingHom.Finite.of_surjective _ (RatModel.stalkMap_pt_surjective X₁.M _))
  obtain ⟨M, q, hn, hq, hpt⟩ := exists_ratModel_normalization X₁.o₁ o₂ Ω₂ κ hκ X₁.M.Z X₁.M.s X₁.M.lft X₁.M.qc
    X₁.M.sep _ hp hst
  exact ⟨M, q, GlobalTheory.IsNormalScheme.of_pred hn, hq, hpt⟩

end GlobalTheory.Poinc
