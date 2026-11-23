import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TanRel
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPolAVSectionInverseImage
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffTopMonEqZero
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.LogHermFormOfUnitDiscriminant

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.MBLow

theorem dualMap_comp_dualMapR {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (f : R →+* R') (g : R' →+* R'') :
    (dualMap g).comp (Chart.dualMapR f) = dualMap (g.comp f) := by
  ext a <;> simp [dualMap, Chart.dualMapR]

theorem dualMap_comp_algebraMap {R R' : Type} [CommRing R] [CommRing R'] (g : R →+* R') :
    (dualMap g).comp (algebraMap R (DualNumber R)) = (algebraMap R' (DualNumber R')).comp g := by
  ext a <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]

theorem isPullback_gen {V : Type} [CommRing V] [IsDomain V] {I : Ideal V} {D : DegData V I}
    {A : PolAV (Sp (FractionRing V))} {G : Over (Sp V)} [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) :
    IsPullback (U.gen.inv.left ≫ pullback.fst G.hom (jK V)) A.A.hom G.hom (spMap (algebraMap V (FractionRing V))) := by
  haveI : IsIso U.gen.inv.left := inferInstanceAs (IsIso ((Over.forget _).map U.gen.inv))
  have sq : IsPullback U.gen.inv.left A.A.hom (pullback.snd G.hom (jK V)) (𝟙 _) :=
    IsPullback.of_horiz_isIso ⟨by simpa using Over.w U.gen.inv⟩
  simpa using sq.paste_horiz (IsPullback.of_hasPullback G.hom (jK V))

theorem vecAt_genFibre : AllV fun {V} _ _ _ {D} {A} {G} _ _ U => ∀ (F : Type) [Field F] [Algebra (FractionRing V) F] (y : epsR V ⟶ G),
    (∃! yA, VecAt U.toUnifPre F y yA) ∧
    (∃! v : epsR (FractionRing V) ⟶ A.A, IsVecOver (algebraMap V (FractionRing V)) (U.gen.inv.left ≫ pullback.fst G.hom (jK V)) y v) ∧
    ∀ (v : epsR (FractionRing V) ⟶ A.A) yA, IsVecOver (algebraMap V (FractionRing V)) (U.gen.inv.left ≫ pullback.fst G.hom (jK V)) y v →
      VecAt U.toUnifPre F y yA → yA ≫ (snd (TFK (R := V) F) A.A).left = spMap (dualMap (algebraMap (FractionRing V) F)) ≫ v.left := by
  intro V _ _ _ _ _ D A G _ _ _ U F _ _ y
  have hφ := isPullback_gen U.toUnifPre
  have hT : IsPullback (fst (TFK (R := V) F) A.A).left (snd (TFK (R := V) F) A.A).left (TFK (R := V) F).hom A.A.hom :=
    IsPullback.of_hasPullback _ _
  have key : ∀ (v : epsR (FractionRing V) ⟶ A.A) yA,
      IsVecOver (algebraMap V (FractionRing V)) (U.gen.inv.left ≫ pullback.fst G.hom (jK V)) y v →
      VecAt U.toUnifPre F y yA →
      yA ≫ (snd (TFK (R := V) F) A.A).left = spMap (dualMap (algebraMap (FractionRing V) F)) ≫ v.left := by
    intro v yA hv hy
    refine hφ.hom_ext ?_ ?_
    · rw [Category.assoc, hy.2, Category.assoc]
      unfold IsVecOver at hv
      rw [hv, ← Category.assoc, spMap_comp_spMap, dualMap_comp_dualMapR]
    · rw [Category.assoc, Over.w (snd _ _), ← Over.w (fst _ _), ← Category.assoc, hy.1, Category.assoc, Over.w v]
      show spMap _ ≫ spMap _ = spMap _ ≫ spMap _
      rw [spMap_comp_spMap, spMap_comp_spMap, dualMap_comp_algebraMap]
  obtain ⟨v, hv, hvu⟩ := existsUnique_isVecOver hφ y
  refine ⟨?_, ⟨v, hv, hvu⟩, key⟩
  have w : (spMap (algebraMap F (DualNumber F)) ≫ (TFK (R := V) F).hom) =
      (spMap (dualMap (algebraMap (FractionRing V) F)) ≫ v.left) ≫ A.A.hom := by
    rw [Category.assoc, Over.w v]
    show spMap _ ≫ spMap _ = spMap _ ≫ spMap _
    rw [spMap_comp_spMap, spMap_comp_spMap, dualMap_comp_algebraMap]
  have hy : VecAt U.toUnifPre F y (hT.lift _ _ w) := by
    refine ⟨hT.lift_fst _ _ w, ?_⟩
    rw [← Category.assoc, hT.lift_snd _ _ w, Category.assoc]
    unfold IsVecOver at hv
    rw [hv, ← Category.assoc, spMap_comp_spMap, dualMap_comp_dualMapR]
  refine ⟨hT.lift _ _ w, hy, fun yA h => ?_⟩
  exact hT.hom_ext ((h.1).trans (hT.lift_fst _ _ w).symm) ((key v yA hv h).trans (hT.lift_snd _ _ w).symm)

end GlobalTheory.MBLow
