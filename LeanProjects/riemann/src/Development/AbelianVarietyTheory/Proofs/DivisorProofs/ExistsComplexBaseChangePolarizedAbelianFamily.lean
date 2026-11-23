import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHolPeriods
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PolPull
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRingActionPullbackCartesianGroupSchemes
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.PolBaseChangeOfRelAmpleLocal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix

noncomputable section

namespace GlobalTheory.PELU

theorem exists_isBC : ∀ (O : Type) [Ring O] (g : ℕ) (R : Type) [CommRing R] (σ : R →+* ℂ) (Λ : Type) (F : Fam R O Λ g),
    ∃ F' : Fam ℂ O Λ g, IsBC F' F σ := by
  intro O _ g R _ σ Λ F
  let f : pullback F.s (spMap σ) ⟶ F.X := pullback.fst _ _
  let A' : Over (pullback F.s (spMap σ)) := (Over.pullback f).obj F.A
  letI : GrpObj A' := Functor.grpObjObj
  have hP : IsGrpPullback A' F.A f (pullback.fst F.A.hom f) := isGrpPullback_pullback F.A f
  haveI : IsCommMonObj A' := GlobalTheory.PolPull.isCommMonObj_of_isGrpPullback hP
  obtain ⟨act', ⟨hh, h1, hm, ha⟩, hc⟩ := GlobalTheory.ActPull.exists_act_pull _ _ f F.A A' _ hP Oᵐᵒᵖ
    (fun a => F.act a.unop) (fun a => F.hom _) F.act_one (fun a b => F.act_mul b.unop a.unop)
    (fun a b => F.act_add _ _)
  have hLB := LB.isLB_pull F.isLB (pullback.fst F.A.hom f)
  have hpol := GlobalTheory.pol_pull _ _ F.A A' f _ F.L (F.L.pull _) F.isLB hLB F.ab hP (GlobalTheory.PolBaseChange.lbIso_refl hLB)
  have hdim : SmoothOfRelativeDimension g A'.hom := by
    have := smoothOfRelativeDimension_isStableUnderBaseChange.{0} g
    exact MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension g) hP.1 F.dim
  let eta' : Λ → (𝟙_ (Over (pullback F.s (spMap σ))) ⟶ A') := fun a =>
    Over.homMk (hP.1.lift (f ≫ (F.eta a).left) (𝟙 _) (by
      rw [Category.assoc, Over.w]; simp)) (hP.1.lift_snd _ _ _)
  refine ⟨Fam.mk (pullback F.s (spMap σ)) (pullback.snd _ _) A' hpol.1 hdim (fun a => act' (MulOpposite.op a))
    (fun a => hh _) h1 (fun a b => by rw [MulOpposite.op_mul]; exact hm _ _)
    (fun a b => by rw [MulOpposite.op_add]; exact ha _ _)
    (F.L.pull (pullback.fst F.A.hom f)) hLB (hpol.2.1 F.ample) eta',
    f, pullback.fst F.A.hom f, IsPullback.of_hasPullback _ _, hP, fun a => hc _,
    GlobalTheory.PolBaseChange.lbIso_refl hLB, fun a => hP.1.lift_fst _ _ _⟩

end GlobalTheory.PELU
