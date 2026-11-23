import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsKerTorusExtension
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteSubextensionCls
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.RigidifiedSymmetricKernelTrivialDescendFieldExt
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PolarisedRingActionDescendOfGenerators
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ProperRelAmpleKTrivOfFieldExtension
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ConnectedSpaceSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.CurveRootGeometry GlobalTheory.NeronCurve GlobalTheory.SS GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TorusPart

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.TorusPart

theorem exists_finite_polDescent : ∀ (O : Type) [CommRing O] [Module.Finite ℤ O] (c : O →+* O) (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω]
    [Algebra.IsAlgebraic K Ω] (B : Over (Sp K)) [GrpObj B], IsAbelianScheme B → ∀ (j₀ : OAct O B) (P : Out.PolAV (Sp Ω))
    (j : OAct O P.A) (ψ : P.A.left ⟶ B.left), IsActPull j j₀ (spMap (algebraMap K Ω)) ψ → IsRosati c P j →
    ∃ F : IntermediateField K Ω, FiniteDimensional K F ∧ ∃ (P₁ : Out.PolAV (Sp F)) (j₁ : OAct O P₁.A)
      (ψ₁ : P₁.A.left ⟶ B.left), IsActPull j₁ j₀ (spMap (algebraMap K F)) ψ₁ ∧ IsRosati c P₁ j₁ := by
  intro O _ _ c K Ω _ _ _ _ B _ hB j₀ P j ψ hpull hros
  haveI := hB.comm
  haveI := hB.proper
  haveI := P.isAb.comm
  obtain ⟨F, hF, H⟩ := GlobalTheory.LBDescent.exists_finite_subextension_cls K Ω B.left P.A.left B.hom P.A.hom ψ
    hpull.1.1 P.L P.isLB
  let f : Sp F ⟶ Sp K := spMap (algebraMap K F)
  let A₁ := (Over.pullback f).obj B
  have hA₁ : IsAbelianScheme A₁ := isAbelianScheme_pullback_obj f B hB
  haveI := hA₁.comm
  haveI := hA₁.smooth
  haveI := hA₁.proper
  have hψ₁ : IsActPull (OAct.pullback f B j₀) j₀ f (pullback.fst B.hom f) := exists_isActPull f j₀
  have hcomp : spMap (algebraMap F Ω) ≫ f = spMap (algebraMap K Ω) := by
    simp only [f, spMap]
    rw [← Spec.map_comp]
    congr 1
  have w : ψ ≫ B.hom = (P.A.hom ≫ spMap (algebraMap F Ω)) ≫ f := by
    rw [Category.assoc, hcomp]
    exact hpull.1.1.w
  let jm : P.A.left ⟶ A₁.left := pullback.lift ψ (P.A.hom ≫ spMap (algebraMap F Ω)) w
  have hjf : jm ≫ pullback.fst B.hom f = ψ := pullback.lift_fst _ _ _
  have hjs : jm ≫ A₁.hom = P.A.hom ≫ spMap (algebraMap F Ω) := pullback.lift_snd _ _ _
  have hj : IsGrpPullback P.A A₁ (spMap (algebraMap F Ω)) jm :=
    IsGrpPullback.cancel hψ₁.1 (hpull.1.congr hcomp.symm hjf.symm) hjs
  obtain ⟨x, hx⟩ := H A₁.left A₁.hom (pullback.fst B.hom f) (IsPullback.of_hasPullback _ _) jm hjf hjs
  obtain ⟨L₁, hL₁, rfl⟩ := CechPic.cls_surj x
  have hw : LBIso P.L (L₁.pull jm) := by
    rw [← CechPic.cls_eq_iff P.isLB (pull_isLB hL₁ jm), CechPic.cls_pull hL₁ jm (pull_isLB hL₁ jm)]
    exact hx.symm
  obtain ⟨g, hg⟩ := GlobalTheory.AbelianDim.exists_relDim F A₁ hA₁
  have hd := GlobalTheory.PolDescent.rigidified_sym_kTriv_descend F Ω (algebraMap F Ω) A₁ P.A jm L₁ P.L hA₁ hj hL₁ P.isLB hw
  have ha := GlobalTheory.AmpleDescent.proper_relAmple_kTriv_of_fieldExtension F Ω (algebraMap F Ω) A₁ P.A jm hj L₁ P.L hL₁
    P.isLB hw P.isAb.proper P.ample P.ktriv
  let P₁ : Out.PolAV (Sp F) :=
    { A := A₁, isAb := hA₁, g := g, smoothDim := hg, L := L₁, isLB := hL₁, rigid := hd.1 P.rigid,
      sym := hd.2.1 P.sym, ample := ha.2.1, ktriv := ha.2.2 }
  have comm : ∀ b, (j.act b).left ≫ jm = jm ≫ ((OAct.pullback f B j₀).act b).left := fun b => by
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, hjf, hψ₁.2 b, ← Category.assoc, hjf, hpull.2 b]
    · show (j.act b).left ≫ jm ≫ A₁.hom = jm ≫ ((OAct.pullback f B j₀).act b).left ≫ A₁.hom
      rw [Over.w ((OAct.pullback f B j₀).act b), hjs, ← Category.assoc, Over.w (j.act b)]
  exact ⟨F, hF, P₁, OAct.pullback f B j₀, pullback.fst B.hom f, hψ₁, fun a =>
    GlobalTheory.RosatiDescent.rosatiAdj_descend (algebraMap F Ω) hA₁ hj hL₁ P.isLB hw (comm a) (comm (c a)) (hros a)⟩

end GlobalTheory.TorusPart
