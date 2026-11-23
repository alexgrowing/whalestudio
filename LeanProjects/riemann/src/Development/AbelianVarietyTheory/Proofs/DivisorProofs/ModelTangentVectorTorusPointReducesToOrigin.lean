import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TanRel
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPolAVSectionInverseImage
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffTopMonEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigValD
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsTorusExtensionPointOfIntegralModelPoint
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.GermEqZeroOfThickenings
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.MBLow.TanRed

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R}
  {D : DegData R I} {A : PolAV (Sp (FractionRing R))} {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]

theorem redE_dualMap (e : ℕ) :
    redE (R ⧸ I ^ (e + 1)) ≫ spMap (dualMap (Ideal.Quotient.mk (I ^ (e + 1)))) = thick R I e ≫ redE R := by
  show spMap _ ≫ spMap _ = Spec.map _ ≫ spMap _
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  ext a <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]

theorem red_lift_eq_eSec (y : epsR R ⟶ G) (hy : IsTangent y) (e : ℕ)
    (ye : Sp (DualNumber (R ⧸ I ^ (e + 1))) ⟶ (thickObj R I e G).left)
    (h1 : ye ≫ (fstG I e G).left = spMap (dualMap (Ideal.Quotient.mk (I ^ (e + 1)))) ≫ y.left) :
    redE (R ⧸ I ^ (e + 1)) ≫ ye = eSec (thickObj R I e G) := by
  rw [← cancel_mono (fstG I e G).left, Category.assoc, h1, ← Category.assoc, redE_dualMap, Category.assoc]
  have hy' : redE R ≫ y.left = η[G].left := hy
  rw [hy']
  exact (UnitValue.eSec_fGl (G := G) e).symm

theorem levels_of_tanRel (U : UnifPre I D A G) (y : epsR R ⟶ G) (hy : IsTangent y) (gm : GtPt D.toPre (epsR R))
    (h : TanRel U y gm) (e : ℕ) :
    eSec (thickObj R I e G) ≫ (U.gt e).pG.left = (thick R I e ≫ redE R) ≫ gm.b.left ∧
    ∀ χ (z : Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) C, Good D.toPre.P.L z C →
      val ((U.gt e).t χ) (eSec (thickObj R I e G)) z C = val (gm.s χ) (thick R I e ≫ redE R) z C := by
  obtain ⟨ye, h1, h2, h3⟩ := h e
  have hr := red_lift_eq_eSec y hy e ye h1
  refine ⟨?_, fun χ z C hC => ?_⟩
  · rw [← hr, Category.assoc, h2, ← Category.assoc, redE_dualMap]
  · rw [← hr, ← redE_dualMap]
    exact (val_pull hC _ _ _).symm.trans ((val_corr hC (h3 χ) _).trans (val_pull hC _ _ _))

theorem gtTan_of_tanRel [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete I R] (U : UnifPre I D A G)
    (y : epsR R ⟶ G) (gm : GtPt D.toPre (epsR R)) (hy : IsTangent y) (h : TanRel U y gm) : GtTan gm := by
  have hL := D.toPre.P.isLB
  have hz := levels_of_tanRel U y hy gm h
  have hb : redE R ≫ gm.b.left = η[D.toPre.P.A].left := hom_ext_of_isHausdorff I fun e =>
    (Category.assoc _ _ _).symm.trans ((hz e).1.symm.trans (UnitValue.eSec_pGl U e))
  obtain ⟨o, ho⟩ := FormalValue.exists_isZero D.toPre (baseOver (Sp R))
  have hob : o.b.left = redE R ≫ gm.b.left := by
    rw [hb, ho.1]
    exact (congrArg (· ≫ η[D.toPre.P.A].left)
      ((Category.comp_id _).symm.trans (Over.w (toUnit (baseOver (Sp R)))))).trans (Category.id_comp _)
  have e₁ := TorusCoord.comp_eq_of_left gm.b o.b (redE R) (𝟙 _) (hob.symm.trans (Category.id_comp _).symm)
  refine ⟨o, ho, hob, fun χ => RedTotal.corr_of_levels I hL (fun W _ f => ?_) (o.isGen χ)
    (DVR.pullGen_isGen _ _ _ _ (gm.isGen χ) _) fun e z J hJ => ?_⟩
  · exact Finset.prod_congr rfl fun k _ => congrArg (fun q => f q ^ DegPre.gtε k)
      ((e₁.1 χ k).trans ((Category.id_comp _).trans (congrFun (TorusCoord.gtφT_eq o.b χ) k).symm)).symm
  · refine ((val_corr hJ (ho.2 χ) _).trans (val_one _)).trans (Eq.trans ?_ (val_pull hJ _ _ _).symm)
    refine Eq.trans ?_ ((hz e).2 χ z J hJ)
    have := (val_corr hJ ((U.gt e).t_unit χ) (𝟙 _)).trans (val_one _)
    rw [val_pull hJ, Category.id_comp] at this
    exact this.symm

theorem main : AllV fun {V} _ _ _ {D} {A} {G} _ _ U => ∀ (y : epsR V ⟶ G) (gm₀ : GtPt D.toPre (epsR V)),
    IsTangent y → TanRel U.toUnifPre y gm₀ → GtTan gm₀ :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ U y gm₀ hy h => gtTan_of_tanRel U.toUnifPre y gm₀ hy h

end GlobalTheory.MBLow.TanRed
