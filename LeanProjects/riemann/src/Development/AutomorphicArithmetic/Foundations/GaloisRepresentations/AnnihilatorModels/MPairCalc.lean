import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PairCalc
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DescendedBundleKernelKilledByIntegerPrimeToP

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod

open GlobalTheory.AbDual GlobalTheory.CechPic GlobalTheory.AbLaw in
theorem UpperTheory.Gal.crystallineComparison.Mod.pairCalc_of :
    PairCalc := by
  intro p _ D R _ b N S s o
  have hcls : ∀ {X Y : Scheme} {L : LB X} (hL : L.IsLB) (f : Y ⟶ X),
      cls (L.pull f) (pull_isLB hL f) = pull f (cls L hL) := by
    intro X Y L hL f
    rw [cls_linComb hL]
    simp
  have move : ∀ {T : Over S} (u : T ⟶ G2 o.A) (F₁ F₂ : G2 o.A ⟶ G2 o.A),
      LBIso (o.P.pull F₁.left) (o.P.pull F₂.left) →
        pull (u ≫ F₁).left (cls o.P o.isLB) = pull (u ≫ F₂).left (cls o.P o.isLB) := by
    intro T u F₁ F₂ h
    rw [Over.comp_left, Over.comp_left, pull_comp, pull_comp, ← hcls o.isLB F₁.left,
      ← hcls o.isLB F₂.left,
      (cls_eq_iff _ _).2 h]
  obtain ⟨e, he, k⟩ := o.kerP
  obtain ⟨t₁, h₁⟩ := o.rig₁
  obtain ⟨t₂, h₂⟩ := o.rig₂
  have hadd := additive_of_cube GlobalTheory.CubeTop.cubeTheorem o.ab o.ab o.isLB ⟨t₁, h₁⟩ ⟨t₂, h₂⟩
  refine ⟨hadd.1, hadd.2, ?_, ⟨e, he, fun T x hx => k T x ((triv_ev_iff o.isLB _ _).2 hx)⟩, ?_⟩
  · intro T x y a
    have h := move (lift x y) _ _ (o.rosati ((algebraMap (𝓞 D.F) D.O) a))
    rw [D.star_F, MulOpposite.unop_op] at h
    unfold evc
    convert h using 3 <;> simp
  · intro o' ψ c
    have hc : cls (Hecke.lbPow o.P c) (LB.isLB_linComb o.isLB _ _) = c • cls o.P o.isLB := by
      unfold Hecke.lbPow
      rw [cls_linComb o.isLB]
      simp [pull_id]
    have hcomp : ∀ {T : Over S} (x y : T ⟶ o.A),
        (lift x y).left ≫ sq2 ψ = (lift (x ≫ ψ) (y ≫ ψ)).left := by
      intro T x y
      unfold sq2
      rw [← Over.comp_left]
      simp
    constructor
    · rintro ⟨h⟩ T x y
      have h' : cls (Hecke.lbPow o.P c) (LB.isLB_linComb o.isLB _ _) =
          cls (o'.P.pull (sq2 ψ)) (pull_isLB o'.isLB (sq2 ψ)) :=
        (cls_eq_iff _ _).2 h
      rw [hc, hcls o'.isLB] at h'
      unfold evc
      rw [← hcomp, pull_comp, ← h', map_nsmul]
    · intro h
      refine ⟨(cls_eq_iff (LB.isLB_linComb o.isLB _ _) (pull_isLB o'.isLB (sq2 ψ))).1 ?_⟩
      have h' := h (G2 o.A) (fst o.A o.A) (snd o.A o.A)
      unfold evc at h'
      rw [← hcomp, pull_comp] at h'
      simp only [lift_fst_snd, Over.id_left, pull_id] at h'
      show cls (Hecke.lbPow o.P c) (LB.isLB_linComb o.isLB _ _) =
        cls (o'.P.pull (sq2 ψ)) (pull_isLB o'.isLB (sq2 ψ))
      rw [hc, hcls o'.isLB, h']
