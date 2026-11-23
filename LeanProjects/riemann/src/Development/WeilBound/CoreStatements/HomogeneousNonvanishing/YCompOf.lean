import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.CInfGood
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BcMapBcVec
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.FlatChernWeightEqOfIndependence
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.OnbMat
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.RegularFormsIsBundleProjectiveCover
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.TwistedDualRegularFormsFiniteCover
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.CuspOnto
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.AdelicGLLastRowAndDetModuleUnderLeftMultiplicati
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
import Development.AutomorphicSpectrum.Statements.GeometryStatements.LamLevel
import Development.AutomorphicSpectrum.Statements.GeometryStatements.ThmFlatA
import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatDegree
import Development.AutomorphicSpectrum.Statements.MetricStatements.SmallOnTower
import Development.AutomorphicSpectrum.Statements.MetricStatements.RankBound
import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart
import Formalism.LocalToGlobal.ProjectiveLattices.CompHt
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.HSClaim
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.ShareLow
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.LineDegreeClosedFormula
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.SpecFirstDetFormNeZero
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootOriginComponentGenericPoint
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComponentGenericIsGenericPoint
import Formalism.LocalToGlobal.ProjectiveLattices.CompFin
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace PositivityTheory.UnitarySelfGeneration

open AlgebraicGeometry CategoryTheory Limits in
theorem exists_component_equiv_of_tower : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (T : Top.RootTower (CMType H) (Dw.p + Dw.q)) (o : TowerOrigin Y T), Top.Given → ∃ κ : Comp Xo c ≃ T.Comp, CompOf o κ := by
  intro E _ _ _ H Dw l Xo c Y T o _
  have hb₁ : IsPreimmersion (spMap (algebraMap (𝓞 c.F) c.F)) :=
    IsPreimmersion.of_isLocalization (nonZeroDivisors (𝓞 c.F)) (S := c.F)
  have hb₂ : AlgebraicGeometry.Flat (spMap (algebraMap (𝓞 c.F) c.F)) := by
    rw [HasRingHomProperty.Spec_iff (P := @AlgebraicGeometry.Flat)]
    have hf : Module.Flat (𝓞 c.F) c.F := IsLocalization.flat c.F (nonZeroDivisors (𝓞 c.F))
    exact RingHom.flat_algebraMap_iff.2 hf
  have := Y.jQ_open
  have hpre : IsPreimmersion Y.j := by unfold Model.j; infer_instance
  have hfl : AlgebraicGeometry.Flat Y.j := by unfold Model.j; infer_instance
  have hg : ∀ Z : Comp Xo c, IsGenericPoint (Formalism.L2.Pj.genPt Z) (Z : Set (Xo.XF c)) := fun Z =>
    Z.2.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents _ Z.2)
  have hmax : ∀ Z : Comp Xo c, ∀ x' : Y.X, x' ⤳ Y.j (Formalism.L2.Pj.genPt Z) → x' = Y.j (Formalism.L2.Pj.genPt Z) := by
    intro Z y hy
    obtain ⟨a, ha, rfl⟩ := AlgebraicGeometry.Flat.generalizingMap Y.j hy
    rw [GlobalTheory.CompanionTheory.Ar.Flat.eq_genericPoint_of_specializes Z.2 (hg Z) a ha]
  choose k hk using fun Z => o.comp_onto _ (hmax Z)
  have hinj : Function.Injective k := by
    intro Z Z' h
    have h1 : Y.j (Formalism.L2.Pj.genPt Z) = Y.j (Formalism.L2.Pj.genPt Z') := by rw [← hk, ← hk, h]
    have h2 := Y.j.isEmbedding.injective h1
    exact Subtype.ext ((hg Z).def.symm.trans (h2 ▸ (hg Z').def))
  have hsurj : Function.Surjective k := by
    intro a
    let Or := o.Or 0 a
    have e₂ : Or.𝔐.f (GlobalTheory.CompanionTheory.Ar.genPt Or.𝔐.ξ) = GlobalTheory.CompanionTheory.Ar.genPt (o.Fx a).ξf := RegAtDom.map_genPt Or.g_over
    have e₃ : Or.𝔐.f (GlobalTheory.CompanionTheory.Ar.genPt Or.𝔐.ξ) = GlobalTheory.CompanionTheory.Ar.genPt Or.𝔐.ξ₀ := RegAtDom.map_genPt Or.𝔐.fn_over
    let η : Sp (T.M 0 a).Ω ⟶ pullback Y.s (spMap (algebraMap (𝓞 c.F) c.F)) :=
      pullback.lift (Or.𝔐.ξ ≫ Or.𝔐.f) (spMap Or.𝔐.cst) (by
        rw [Category.assoc, Or.𝔐.cst_over, KapEquiv.spMap_comp_eq])
    have hη : pullback.fst Y.s (spMap (algebraMap (𝓞 c.F) c.F)) (GlobalTheory.CompanionTheory.Ar.genPt η) =
        GlobalTheory.CompanionTheory.Ar.genPt Or.𝔐.ξ₀ := by
      rw [← e₃]
      refine (Scheme.Hom.comp_apply η _ _).symm.trans ?_
      rw [show η ≫ pullback.fst _ _ = Or.𝔐.ξ ≫ Or.𝔐.f from pullback.lift_fst _ _ _]
      exact Scheme.Hom.comp_apply _ _ _
    have hfin : Finite (Comp Xo c) := Formalism.L2.Pj.CompFin.finite_comp Xo c
    have hcl : IsClosed (⋃ Z : Comp Xo c, closure {Y.jQ (Formalism.L2.Pj.genPt Z)}) :=
      isClosed_iUnion_of_finite fun _ => isClosed_closure
    have hsub : Set.range Y.jQ ⊆ ⋃ Z : Comp Xo c, closure {Y.jQ (Formalism.L2.Pj.genPt Z)} := by
      rintro _ ⟨p, rfl⟩
      refine Set.mem_iUnion.2 ⟨⟨irreducibleComponent p, irreducibleComponent_mem_irreducibleComponents p⟩, ?_⟩
      exact specializes_iff_mem_closure.1 (((hg _).specializes mem_irreducibleComponent).map Y.jQ.continuous)
    obtain ⟨Z, hZ⟩ := Set.mem_iUnion.1 (closure_minimal hsub hcl (Y.jQ_dense (GlobalTheory.CompanionTheory.Ar.genPt η)))
    have h1 := (specializes_iff_mem_closure.2 hZ).map (pullback.fst Y.s (spMap (algebraMap (𝓞 c.F) c.F))).continuous
    rw [hη] at h1
    have h2 := GlobalTheory.CompanionTheory.Ar.CmpHodgeDiag.eq_of_specializes Or.𝔐.gen₀ h1
    refine ⟨Z, o.comp_inj _ _ ?_⟩
    rw [hk, ← e₂, e₃, ← h2]
    exact Scheme.Hom.comp_apply _ _ _
  exact ⟨Equiv.ofBijective k ⟨hinj, hsurj⟩, hk⟩

theorem y_comp_of : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (T : Top.RootTower (CMType H) (Dw.p + Dw.q)) (o : TowerOrigin Y T), Top.Given → ∃ κ : Comp Xo c ≃ T.Comp, CompOf o κ := exists_component_equiv_of_tower

end PositivityTheory.UnitarySelfGeneration
