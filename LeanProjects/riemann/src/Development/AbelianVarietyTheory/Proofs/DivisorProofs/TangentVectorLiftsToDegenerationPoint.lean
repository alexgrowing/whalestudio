import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TanRel
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPolAVSectionInverseImage
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffTopMonEqZero
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsTorusExtensionPointOfIntegralModelPoint
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.GermEqZeroOfThickenings

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.MBLow.TanLift

theorem isLocalRing_dualNumber (R : Type) [CommRing R] [IsLocalRing R] : IsLocalRing (DualNumber R) :=
  have : Nontrivial (DualNumber R) := (TrivSqZeroExt.inl_injective (R := R) (M := R)).nontrivial
  IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun x => by
    rw [TrivSqZeroExt.isUnit_iff_isUnit_fst, TrivSqZeroExt.isUnit_iff_isUnit_fst]
    simpa using IsLocalRing.isUnit_or_isUnit_one_sub_self x.fst

theorem dualMap_over {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') :
    spMap (dualMap f) ≫ (epsR R).hom = spMap (algebraMap R' (DualNumber R')) ≫ spMap f := by
  show spMap _ ≫ spMap _ = _
  rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
  congr 2
  ext a <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]

theorem redE_over (R : Type) [CommRing R] : redE R ≫ (epsR R).hom = 𝟙 _ := by
  show spMap _ ≫ spMap _ = _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← Spec.map_id]
  congr 2

variable {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] {I : Ideal R} [IsAdicComplete I R]
  {D : DegData R I} {A : PolAV (Sp (FractionRing R))} {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]

theorem exists_tan (U : UnifPre I D A G) (y : epsR R ⟶ G) (hy : IsTangent y) :
    ∃ gm : GtPt D.toPre (epsR R), TanRel U y gm ∧ GtTan gm ∧ IsTangent gm.b := by
  have hL := D.toPre.P.isLB
  have := isLocalRing_dualNumber R
  have : Module.Finite R (DualNumber R) := inferInstanceAs (Module.Finite R (R × R))
  have := isAdicComplete_map_of_finite I (DualNumber R)
  obtain ⟨g, hg⟩ := IntegralGt.exists_gtPt U (φ := algebraMap R (DualNumber R)) y
  have hz := fun e => hg e _ (thick R I e ≫ redE R) (eSec (thickObj R I e G))
    ((UnitValue.eSec_fGl (G := G) e).trans ((congrArg (thick R I e ≫ ·) hy.symm).trans (Category.assoc _ _ _).symm))
  have hb : redE R ≫ g.b.left = η[D.toPre.P.A].left := hom_ext_of_isHausdorff I fun e =>
    (Category.assoc _ _ _).symm.trans ((hz e).1.symm.trans (UnitValue.eSec_pGl U e))
  refine ⟨g, fun e => ?_, ?_, hb⟩
  · have w : (spMap (dualMap (Ideal.Quotient.mk (I ^ (e + 1)))) ≫ y.left) ≫ G.hom =
        spMap (algebraMap _ (DualNumber (R ⧸ I ^ (e + 1)))) ≫ thick R I e := by
      rw [Category.assoc, Over.w y]; exact dualMap_over _
    have h₁ : pullback.lift _ _ w ≫ (fstG I e G).left = _ := pullback.lift_fst _ _ _
    obtain ⟨h₂, h₃⟩ := hg e _ _ _ h₁
    refine ⟨_, h₁, h₂, fun χ => corr_of_val hL fun z J hJ => ?_⟩
    refine (val_pull hJ _ _ _).trans (Eq.trans ?_ (val_pull hJ _ _ _).symm)
    rw [Category.id_comp, Category.id_comp]
    exact h₃ χ z J hJ
  · obtain ⟨o, ho⟩ := FormalValue.exists_isZero D.toPre (baseOver (Sp R))
    have hob : o.b.left = redE R ≫ g.b.left := by
      rw [hb, ho.1]
      exact (congrArg (· ≫ η[D.toPre.P.A].left)
        ((Category.comp_id _).symm.trans (Over.w (toUnit (baseOver (Sp R)))))).trans (Category.id_comp _)
    have e₁ := TorusCoord.comp_eq_of_left g.b o.b (redE R) (𝟙 _) (hob.symm.trans (Category.id_comp _).symm)
    refine ⟨o, ho, hob, fun χ => RedTotal.corr_of_levels I hL (fun W _ f => ?_) (o.isGen χ)
      (DVR.pullGen_isGen _ _ _ _ (g.isGen χ) _) fun e z J hJ => ?_⟩
    · exact Finset.prod_congr rfl fun k _ => congrArg (fun q => f q ^ DegPre.gtε k)
        ((e₁.1 χ k).trans ((Category.id_comp _).trans (congrFun (TorusCoord.gtφT_eq o.b χ) k).symm)).symm
    · refine ((val_corr hJ (ho.2 χ) _).trans (val_one _)).trans (Eq.trans ?_ (val_pull hJ _ _ _).symm)
      refine Eq.trans ?_ ((hz e).2 χ z J hJ)
      have := (val_corr hJ ((U.gt e).t_unit χ) (𝟙 _)).trans (val_one _)
      rw [val_pull hJ, Category.id_comp] at this
      exact this.symm

theorem main : AllV fun {V} _ _ _ {D} {A} {G} _ _ U => ∀ y : epsR V ⟶ G, IsTangent y →
    ∃ gm : GtPt D.toPre (epsR V), TanRel U.toUnifPre y gm ∧ GtTan gm ∧ IsTangent gm.b :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ U y hy => exists_tan U.toUnifPre y hy

end GlobalTheory.MBLow.TanLift

end
