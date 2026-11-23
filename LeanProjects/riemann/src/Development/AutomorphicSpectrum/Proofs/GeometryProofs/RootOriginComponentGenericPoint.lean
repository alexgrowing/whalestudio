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
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootOriginGenericFrameStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelPullbackEquivalence
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.StalkSpecializesBijective
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.NonemptyCptOverOfFlatPreimmersion
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCompComparisonMiddle
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlagEqualChangeLowerTriangular
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFramedPointBaseChangeAlgebraMap
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrameLawsOfModuli
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.KapEquiv

theorem spMap_comp_eq {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  rw [← Spec.map_comp]; rfl

theorem exists_kap_equiv : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (SS : Finset ℕ) (RM : Top.RootModel (CMType H) (Dw.p + Dw.q)) (Sys : PB.AnSys (Top.dimFl (CMType H) (Dw.p + Dw.q)) (Option (RootIx Dw))) (Fx : FixedData Y Sys) (Or : RootOrigin Y SS RM Fx) (Z : Comp Xo c), GlobalTheory.CompanionTheory.Ar.genPt Fx.ξf = Y.j (Formalism.L2.Pj.genPt Z) → ∃ ψ : kap Z ≃+* Or.𝔐.Ω₀, spMap ψ.toRingHom ≫ genSp Z ≫ Y.j = Or.𝔐.ξ₀ ∧ ∀ a : c.F, Or.𝔐.fn (ψ (algebraMap c.F (kap Z) a)) = Or.𝔐.cst a := by
  intro E _ _ _ H Dw l Xo c Y SS RM Sys Fx Or Z hgen
  have hb₁ : IsPreimmersion (spMap (algebraMap (𝓞 c.F) c.F)) :=
    IsPreimmersion.of_isLocalization (nonZeroDivisors (𝓞 c.F)) (S := c.F)
  have hb₂ : Flat (spMap (algebraMap (𝓞 c.F) c.F)) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    have hf : Module.Flat (𝓞 c.F) c.F := IsLocalization.flat c.F (nonZeroDivisors (𝓞 c.F))
    exact RingHom.flat_algebraMap_iff.2 hf
  have := Y.jQ_open
  have : IsPreimmersion Y.j := by unfold Model.j; infer_instance
  have : Flat Y.j := by unfold Model.j; infer_instance
  have hg : IsGenericPoint (Formalism.L2.Pj.genPt Z) (Z : Set (Xo.XF c)) :=
    Z.2.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents _ Z.2)
  have hC : IsCptGen (Ω := Formalism.L2.Pj.kap Z) (Formalism.L2.Pj.genSp Z ≫ Y.j) :=
    GlobalTheory.CompanionTheory.Ar.Flat.isCptGen_comp_of_flat_preimmersion Y.j (fun x => (Y.normal x).1) (Formalism.L2.Pj.genPt Z)
      (GlobalTheory.CompanionTheory.Ar.Flat.eq_genericPoint_of_specializes Z.2 hg)
  have e₁ : GlobalTheory.CompanionTheory.Ar.genPt (Ω := Formalism.L2.Pj.kap Z) (Formalism.L2.Pj.genSp Z ≫ Y.j) = Y.j (Formalism.L2.Pj.genPt Z) :=
    congrArg Y.j ((Xo.XF c).fromSpecResidueField_apply (Formalism.L2.Pj.genPt Z) _)
  have e₂ : Or.𝔐.f (GlobalTheory.CompanionTheory.Ar.genPt Or.𝔐.ξ) = GlobalTheory.CompanionTheory.Ar.genPt Fx.ξf := RegAtDom.map_genPt Or.g_over
  have e₃ : Or.𝔐.f (GlobalTheory.CompanionTheory.Ar.genPt Or.𝔐.ξ) = GlobalTheory.CompanionTheory.Ar.genPt Or.𝔐.ξ₀ := RegAtDom.map_genPt Or.𝔐.fn_over
  obtain ⟨ψ, hψ⟩ := GlobalTheory.CompanionTheory.Ar.FlagPull.exists_iso hC Or.𝔐.gen₀ (e₁.trans (hgen.symm.trans (e₂.symm.trans e₃)))
  refine ⟨ψ, hψ, ?_⟩
  have hsY : Y.j ≫ Y.s = Formalism.L2.Pj.strK ≫ spMap (algebraMap (𝓞 c.F) c.F) := by
    rw [Model.j, Category.assoc, pullback.condition, ← Category.assoc, Y.jQ_over]
  have h1 : Formalism.L2.Pj.genSp Z ≫ Formalism.L2.Pj.strK = spMap (algebraMap c.F (Formalism.L2.Pj.kap Z)) :=
    (Spec.map_preimage _).symm
  have hfn : Or.𝔐.ξ ≫ Or.𝔐.f = spMap Or.𝔐.fn ≫ Or.𝔐.ξ₀ := Or.𝔐.fn_over
  let i : c.F →+* RM.Ω := (Or.𝔐.fn.comp ψ.toRingHom).comp (algebraMap c.F (Formalism.L2.Pj.kap Z))
  have e0 : i.comp (algebraMap (𝓞 c.F) c.F) = Or.𝔐.cst.comp (algebraMap (𝓞 c.F) c.F) := by
    have hS : spMap (i.comp (algebraMap (𝓞 c.F) c.F)) = spMap (Or.𝔐.cst.comp (algebraMap (𝓞 c.F) c.F)) := by
      refine Eq.trans ?_ Or.𝔐.cst_over
      have h3 : Or.𝔐.ξ ≫ Or.𝔐.f ≫ Y.s = spMap Or.𝔐.fn ≫ spMap ψ.toRingHom ≫
          (Formalism.L2.Pj.genSp Z ≫ Formalism.L2.Pj.strK) ≫ spMap (algebraMap (𝓞 c.F) c.F) := by
        rw [← Category.assoc, hfn, ← hψ]
        simp only [Category.assoc]
        rw [hsY]
      rw [h3, h1]
      simp only [i, spMap_comp_eq, Category.assoc]
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective hS)
  have e4 : i = Or.𝔐.cst := IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 c.F)) e0
  intro a
  exact congrArg (fun φ : c.F →+* RM.Ω => φ a) e4

end GlobalTheory.CompanionTheory.Ar.KapEquiv
