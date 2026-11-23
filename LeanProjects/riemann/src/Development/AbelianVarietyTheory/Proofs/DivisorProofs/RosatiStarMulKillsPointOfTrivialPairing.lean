import Development.AbelianVarietyTheory.Definitions.Divisors.FacAlg
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalEnd
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsHeckeQuotientTriple
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SmoothOfRelativeDimensionOfCharZero
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RosatiAdjointAbelianPartAndClassifyingMapLinear

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

open GlobalTheory.CechPic

theorem lam_rosati_field (K : Type) [Field K] (P : PolAV (Sp K)) (O : Type) [Ring O] [StarRing O] (oA : P.OAct O)
    (o : O) {T' : Over (Sp K)} (x z : T' ⟶ P.A) :
    haveI := P.isAb.comm
    lam (cls P.L P.isLB) (x ≫ oA.act (star o)) z = lam (cls P.L P.isLB) x (z ≫ oA.act o) := by
  haveI := P.isAb.comm
  haveI := oA.hom (star o)
  haveI := oA.hom o
  have hr := oA.rosati (star o)
  rw [star_star] at hr
  obtain ⟨u, hu, -⟩ := exists_ros GlobalTheory.globalFns_holds P.isAb P.isLB _ _ hr
  have h := GlobalTheory.EndRosati.cls_of_rosati P.isLB u hu x z
  show _ - _ - _ + _ = _ - _ - _ + _
  rw [h]

theorem kill_of_lam_triv : ∀ (K : Type) [Field K] (P : PolAV (Sp K)) (O : Type) [Ring O] [StarRing O] (oA : P.OAct O) (e f : O) (H : Over (Sp K)) (a : H ⟶ P.A) (r : P.A ⟶ H), r ≫ a = oA.act e → ∀ (T : Over (Sp K)) (y : T ⟶ P.A), (∃ t : LB.Gen (letI := P.isAb.comm; (abelian₂ P.A P.L).pull (lift (snd H T ≫ y) (fst H T ≫ a ≫ oA.act f) : H ⊗ T ⟶ G2 P.A).left), t.IsGen) → y ≫ oA.act (star e * star f) = toUnit T ≫ η[P.A] := by
  intro K _ P O _ _ oA e f H a r hra T y ⟨t, ht⟩
  haveI := P.isAb.comm
  have h0 : lam (cls P.L P.isLB) (snd H T ≫ y) (fst H T ≫ a ≫ oA.act f) = 0 := by
    have := (cls_eq_zero_iff (pull_isLB (GlobalTheory.FullSiegel.isLB_lam P.isLB) _)).2 ⟨t, ht⟩
    rwa [GlobalTheory.FullSiegel.cls_lam_pull P.isLB] at this
  have h1 : lam (cls P.L P.isLB) (fst T P.A ≫ y) ((snd T P.A ≫ oA.act e) ≫ oA.act f) = 0 := by
    have := congrArg (pull (lift (snd T P.A ≫ r) (fst T P.A)).left) h0
    rw [pull_lam, map_zero, lift_snd_assoc, lift_fst_assoc, Category.assoc, reassoc_of% hra] at this
    rw [Category.assoc]
    exact this
  have h2 := (lam_rosati_field K P O oA f _ _).trans h1
  have h3 := (lam_rosati_field K P O oA e _ (snd T P.A)).trans h2
  have hb : ((fst T P.A ≫ y) ≫ oA.act (star f)) ≫ oA.act (star e) = fst T P.A ≫ y ≫ oA.act (star e * star f) := by
    rw [oA.map_mul]; simp only [Category.assoc]
  rw [hb] at h3
  have h4 := congrArg (pull (lift (snd P.A T) (fst P.A T)).left) h3
  rw [pull_lam, map_zero, lift_fst_assoc, lift_snd] at h4
  have hg : ∃ t : ((abelian₂ P.A P.L).pull (lift (snd P.A T ≫ y ≫ oA.act (star e * star f)) (fst P.A T)).left).Gen,
      t.IsGen := by
    refine (cls_eq_zero_iff (pull_isLB (GlobalTheory.FullSiegel.isLB_lam P.isLB) _)).1 ?_
    rw [GlobalTheory.FullSiegel.cls_lam_pull P.isLB]
    exact h4
  exact (GlobalTheory.FullSiegel.eq_one_of_lam_triv P.isLB P.rigid P.ktriv T _ hg).trans (Hom.one_def ..)

end GlobalTheory.Mum
