import Mathlib
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LieLatticeLocalBasisDescription
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LnStepFalse
open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj
open GlobalTheory.TrueGeo GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.Toroidal GlobalTheory.LocM.Frm GlobalTheory.HeightParts
open GlobalTheory.GradedNorm GlobalTheory.LieHt
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.LieSmooth

open MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Semi
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LieHt.CoverGlue

theorem fst_dualMap {R F : Type} [CommRing R] [CommRing F] (f : R →+* F) :
    spMap f ≫ spMap (TrivSqZeroExt.fstHom R R R).toRingHom =
      spMap (TrivSqZeroExt.fstHom F F F).toRingHom ≫ spMap (dualMap f) := by
  refine (spMap_comp_spMap _ _).trans (Eq.trans ?_ (spMap_comp_spMap _ _).symm)
  congr 1
  ext a <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]

theorem dualMap_algebraMap {R F : Type} [CommRing R] [CommRing F] (f : R →+* F) :
    spMap (dualMap f) ≫ spMap (algebraMap R (DualNumber R)) = spMap (algebraMap F (DualNumber F)) ≫ spMap f :=
  (GlobalTheory.CM.LieGlue.isPullback_dualMap f).w

theorem exists_tan_of_cover : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}} (t : SAB H X) {R F : Type} [CommRing R] [CommRing F] (f : R →+* F), Function.Injective f → ∀ {m : ℕ} (r : Fin m → R), Ideal.span (Set.range r) = ⊤ → ∀ (g : ∀ i, Localization.Away (r i) →+* F), (∀ i, (g i).comp (algebraMap R (Localization.Away (r i))) = f) → ∀ {xO : Sp R ⟶ X} {xF : Sp F ⟶ X} (hx : spMap f ≫ xO = xF) (hxi : ∀ i, spMap (g i) ≫ spMap (algebraMap R (Localization.Away (r i))) ≫ xO = xF) (w : TanM xF t.G) (u : ∀ i, TanM (spMap (algebraMap R (Localization.Away (r i))) ≫ xO) t.G), (∀ i, bcTan (g i) (hxi i) (u i) = w) → ∃ v : TanM xO t.G, bcTan f hx v = w := by
  intro E _ _ _ H X t R F _ _ f hf m r hr g hg xO xF hx hxi w u hu
  have hsep : IsSeparated t.G.hom := t.semi.separated
  have hsep' : IsSeparated ((Over.pullback xO).obj t.G).hom :=
    inferInstanceAs (IsSeparated (Limits.pullback.snd t.G.hom xO))
  have hw := GlobalTheory.LieMet.isTan_tv w
  have hw1 : (tv w).left ≫ t.G.hom = (spMap (algebraMap F (DualNumber F)) ≫ spMap f) ≫ xO := by
    rw [Category.assoc, hx]; exact hw.1
  have hu1 : ∀ i, (tv (u i)).left ≫ t.G.hom =
      (spMap (algebraMap _ (DualNumber (Localization.Away (r i)))) ≫
        spMap (algebraMap R (Localization.Away (r i)))) ≫ xO := fun i => by
    rw [Category.assoc]; exact (GlobalTheory.LieMet.isTan_tv (u i)).1
  obtain ⟨v, hv⟩ := GlobalTheory.CM.LieGlue.exists_glue f hf (A := (Over.pullback xO).obj t.G) r hr g hg
    (Limits.pullback.lift _ _ hw1) (fun i => Limits.pullback.lift _ _ (hu1 i))
    (fun i => Limits.pullback.lift_snd _ _ _) (fun i => by
      refine Limits.pullback.hom_ext ?_ ?_
      · refine (Category.assoc _ _ _).trans ?_
        refine (congrArg (_ ≫ ·) (Limits.pullback.lift_fst _ _ _)).trans ?_
        refine Eq.trans ?_ (Limits.pullback.lift_fst _ _ _).symm
        rw [← hu i]
        rfl
      · refine (Category.assoc _ _ _).trans ?_
        refine (congrArg (_ ≫ ·) (Limits.pullback.lift_snd _ _ _)).trans ?_
        refine Eq.trans ?_ (Limits.pullback.lift_snd _ _ _).symm
        refine (Category.assoc _ _ _).symm.trans ?_
        refine (congrArg (· ≫ _) (dualMap_algebraMap (g i))).trans ?_
        rw [Category.assoc, spMap_comp_spMap (algebraMap R _) (g i), hg i])
  have hv' : spMap (dualMap f) ≫ (v.left ≫ Limits.pullback.fst t.G.hom xO) = (tv w).left := by
    refine (Category.assoc _ _ _).symm.trans ?_
    exact (congrArg (· ≫ _) hv).trans (Limits.pullback.lift_fst _ _ _)
  have h1 : (v.left ≫ Limits.pullback.fst t.G.hom xO) ≫ t.G.hom = spMap (algebraMap R (DualNumber R)) ≫ xO := by
    rw [Category.assoc, Limits.pullback.condition, ← Category.assoc]
    exact congrArg (· ≫ xO) (Over.w v)
  have ht : IsTanAtG t xO (v.left ≫ Limits.pullback.fst t.G.hom xO) := by
    refine ⟨h1, ?_⟩
    have := GlobalTheory.ExtUnique.isSchemeTheoreticallyDominant_spec_of_injective (CommRingCat.ofHom f) hf
    refine GlobalTheory.ExtUnique.hom_ext_of_dominant t.G.hom ?_ (spMap f) ?_
    · rw [Category.assoc, h1, ← Category.assoc]
      refine Eq.trans ?_ (Over.w (1 : Over.mk xO ⟶ t.G)).symm
      refine Eq.trans (congrArg (· ≫ xO) ?_) (Category.id_comp xO)
      refine (spMap_comp_spMap _ _).trans ?_
      refine Eq.trans ?_ (Spec.map_id (CommRingCat.of R))
      congr 1
    · rw [← Category.assoc, fst_dualMap, Category.assoc, hv', hw.2]
      exact (congrArg (·.left)
        (MonObj.comp_one (M := t.G) (Over.homMk (spMap f) hx : Over.mk xF ⟶ Over.mk xO))).symm
  exact ⟨GlobalTheory.LieMet.tanOf ht, GlobalTheory.LieMet.tan_ext hv'⟩

end GlobalTheory.LieHt.CoverGlue
