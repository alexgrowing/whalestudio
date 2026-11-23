import Development.AbelianVarietyTheory.Definitions.Divisors.TanRel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TrVal
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPolAVSectionInverseImage
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffTopMonEqZero
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.MBLow

theorem trF_dualPoint_of_isPull : ∀ (V : Type) [CommRing V] [IsDomain V] (D : DegPre V) (C : Type) [Field C] [Algebra (FractionRing V) C] (gm₀ : GtPt D (epsR V)) (gm : GtPt D (TE V C)), GtPt.IsPull (spMap (dualMap (toF V C))) gm₀ gm → ∀ mu : D.X, ((lift (Over.homMk (spMap (algebraMap C (DualNumber C))) rfl : TE V C ⟶ TF (R := V) C) gm.b).left ≫ (DegPre.trF D C mu).left) ≫ (DegPre.prB D C).left = spMap (dualMap (toF V C)) ≫ (padd D.P.A gm₀.b (toUnit _ ≫ D.c mu)).left ∧ (padd D.P.A gm₀.b (toUnit _ ≫ D.c mu)).left ≫ D.P.A.hom = spMap (algebraMap V (DualNumber V)) ∧ ((lift (Over.homMk (spMap (algebraMap C (DualNumber C))) rfl : TE V C ⟶ TF (R := V) C) gm.b).left ≫ (DegPre.trF D C mu).left) ≫ (fst (TF (R := V) C) D.P.A).left = spMap (algebraMap C (DualNumber C)) := by
  intro V _ _ D C _ _ gm₀ gm hp mu
  have hsq : spMap (dualMap (toF V C)) ≫ (epsR V).hom = (TE V C).hom := by
    simp only [epsR, TE, TF, jFK, jK, spMap, Over.mk_hom, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext r <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]
  let k : TE V C ⟶ epsR V := Over.homMk (spMap (dualMap (toF V C))) hsq
  have hb : gm.b = k ≫ gm₀.b := by
    ext1
    simpa [k] using hp.1
  set e : TE V C ⟶ TF (R := V) C := Over.homMk (spMap (algebraMap C (DualNumber C))) rfl with he
  refine ⟨?_, Over.w _, ?_⟩
  · have h1 : lift e gm.b ≫ DegPre.trF D C mu ≫ DegPre.prB D C = k ≫ padd D.P.A gm₀.b (toUnit _ ≫ D.c mu) := by
      simp only [DegPre.trF, DegPre.prB, lift_snd, padd, comp_lift_assoc, comp_lift, hb, Category.assoc, comp_toUnit_assoc]
    have h2 := congrArg CommaMorphism.left h1
    simpa [k] using h2
  · have h1 : lift e gm.b ≫ DegPre.trF D C mu ≫ fst _ _ = e := by
      simp [DegPre.trF]
    have h2 := congrArg CommaMorphism.left h1
    simpa [he] using h2

end GlobalTheory.MBLow

end
