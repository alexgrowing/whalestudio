import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsFrameVec
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieLatticeEvalFractionField
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsExcisionNbhdAway
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.GenericExistsUniqueOActOfIsGrpPullback
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SpecFracExt
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootOriginFrameLocalBound
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open AlgebraicGeometry CategoryTheory
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.LieBasis

open Limits MonObj

theorem exists_val_of_isTan : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) (tX : SAB H X) (T : CDVR) (zV : Spec (CommRingCat.of T.V) ⟶ X) (G : SAB H (Spec (CommRingCat.of T.V))) (Ψ : G.G.left ⟶ tX.G.left), IsGrpPullback G.G tX.G zV Ψ → ∀ (EC : Type) [AddCommGroup EC] [Module T.Fr EC] (MC : LieModel tX.G (FinRd.Roots.gen T zV) EC) (v : epsOver T.V T.V ⟶ G.G), IsTan v → ∃ w : EC, (MC.pt w).left = Spec.map (CommRingCat.ofHom (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap T.V T.Fr))) ≫ v.left ≫ Ψ := by
  intro E _ _ _ H X tX T zV G Ψ hΨ EC _ _ MC v hv
  have hbase : Spec.map (CommRingCat.ofHom (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap T.V T.Fr))) ≫ (epsOver T.V T.V).hom =
      Spec.map (CommRingCat.ofHom (algebraMap T.Fr (DualNumber T.Fr))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap T.V T.Fr)) := by
    change Spec.map _ ≫ Spec.map _ = _
    rw [LieTangent.spec_comp, LieTangent.spec_comp]
    congr 2
    ext a <;> simp [GlobalTheory.CompanionTheory.Ar.dualMap, TrivSqZeroExt.algebraMap_eq_inl]
  have hover : (Spec.map (CommRingCat.ofHom (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap T.V T.Fr))) ≫ v.left ≫ Ψ) ≫ tX.G.hom =
      (epsAt (FinRd.Roots.gen T zV)).hom := by
    have hw : v.left ≫ G.G.hom = (epsOver T.V T.V).hom := Over.w v
    rw [Category.assoc, Category.assoc, hΨ.1.w, ← Category.assoc v.left, hw, ← Category.assoc, hbase,
      Category.assoc]
    rfl
  let vt : epsAt (FinRd.Roots.gen T zV) ⟶ tX.G := Over.homMk _ hover
  have ht : GlobalTheory.CompanionTheory.Ar.IsTanAt tX.G (FinRd.Roots.gen T zV) vt := by
    have hv' : Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom T.V T.V T.V).toRingHom) ≫ v.left =
        (1 : ptOver T.V T.V ⟶ G.G).left := hv
    have h1 := FrameValue.one_left_grp hΨ (Spec.map (CommRingCat.ofHom (algebraMap T.V T.V))) _ rfl
    have hp : Spec.map (CommRingCat.ofHom (algebraMap T.V T.Fr)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap T.V T.V)) ≫ zV = FinRd.Roots.gen T zV := by
      rw [Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id, Category.id_comp]
    have h2 := FrameValue.one_left_pull (G := tX.G) (Spec.map (CommRingCat.ofHom (algebraMap T.V T.Fr))) _ _ hp
    change Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom T.Fr T.Fr T.Fr).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap T.V T.Fr))) ≫ v.left ≫ Ψ = _
    rw [← Category.assoc, LieTangent.spec_fst_dual, Category.assoc, ← Category.assoc _ v.left Ψ, hv']
    exact (congrArg (fun u => Spec.map (CommRingCat.ofHom (algebraMap T.V T.Fr)) ≫ u) h1).trans h2
  obtain ⟨w, hw⟩ := MC.onto vt ht
  exact ⟨w, congrArg (fun u => u.left) hw⟩

end GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.LieBasis
