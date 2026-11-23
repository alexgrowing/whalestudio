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
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LabelSigBijective
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FormOffSpecializationRingStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootOriginFrameHeightStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootOriginGenericFrameBoundStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootOriginFrameSectionBoundStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootOriginFrameDegreeBoundStatement
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.Rec

theorem latExp_eq (E : Type) [Field E] [NumberField E] (SS : Finset ℕ) (p : ℕ) :
    Small.latExp E SS p = if p ∈ SS then 1 / ((p : ℝ) - 1) + (if p = 2 then 1 else 0) +
      (padicValInt p (discr E) : ℝ) / Module.finrank ℚ E else 0 := by
  unfold Small.latExp Small.htExp
  by_cases h : p ∈ SS
  · by_cases h2 : p = 2
    · subst h2
      norm_num
    · simp [h, h2]
  · simp [h]

theorem read_fin : (Top.Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsGalois ℚ E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (h : GenFrEx Xo c) (e : Comp Xo c → Rul Xo c), CompLaws U h e → Ref.UnifAll Xo c → ∀ (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (SS : Finset ℕ) (RM : Top.RootModel (CMType H) (Dw.p + Dw.q)) (Sys : PB.AnSys (Top.dimFl (CMType H) (Dw.p + Dw.q)) (Option (RootIx Dw))) (Fx : FixedData Y Sys) (Or : RootOrigin Y SS RM Fx) (Fr : Small.GenFrame Or) (Z : Comp Xo c) (Rd : Reading Fr h Z), Or.𝔐.OmVB → (∀ p : ℕ, p.Prime → (p : ℤ) ∣ discr E → p ∈ SS) → ∃ u : MRing RM.ι, Small.IsFormOff (mCoordIdeal RM.y) u ∧ ∀ (p : ℕ) [Fact p.Prime], ∀ z ∈ Small.algPts p (mCoordIdeal RM.y), MvPolynomial.aeval z u ≠ 0 → ∃ (la : HeightOneSpectrum (𝓞 c.F)) (y : (Ref.pjSys Xo c).Pt la) (rec : RootIx Dw → ℝ), (p : 𝓞 c.F) ∈ la.asIdeal ∧ (Ref.pjSys Xo c).val y (e Z) = 0 ∧ (∀ r', 0 < rec r' ∧ |Real.log (Small.supMet (RM.xdeg r') z) - Real.log (rec r')| ≤ (if p ∈ SS then 1 / ((p : ℝ) - 1) + (if p = 2 then 1 else 0) + (padicValInt p (discr E) : ℝ) / Module.finrank ℚ E else 0) * Real.log p) ∧ ∀ (a : WZ E) (n' : Option (RootIx Dw) → ℤ), (∀ j, (n' j : ℝ) = RM.coef (towerWt Dw a) 0 j) → ∀ f ∈ secZ Xo c a, ∃ v, Small.HasVal RM.y (Top.combLine (RM.line 1) n').a (Fr.rd f * (∏ r', Or.e r' ^ (-n' (some r')))) z v ∧ ((Ref.pjSys Xo c).val y f = ⊤ → v = 0) ∧ ∀ s : ℝ, (Ref.pjSys Xo c).val y f = ((ramOverZ la * s : ℝ) : EReal) → ‖v‖ = (p : ℝ) ^ (-s) * ∏ r', rec r' ^ n' (some r')) := by
  intro hG E _ _ _ _ H Dw l Xo c r U h e hL hUn O _ β Y SS RM Sys Fx Or Fr Z Rd hOm hram
  haveI : CharZero RM.Ω := charZero_of_injective_ringHom Or.𝔐.cst.injective
  obtain ⟨B, hB⟩ := GlobalTheory.T.root_origin_frame_height E H Dw l Xo c O β Y SS RM Sys Fx Or Fr
  obtain ⟨u, hu, hA⟩ := GlobalTheory.T.form_off_specialization_ring RM.K RM.ι RM.Ω RM.y RM.birational
    (by classical exact B ∪ Finset.univ.image (fun x : Σ k : RM.K, RM.ι k × RM.ι k => RM.y ⟨x.1, x.2.1⟩ / RM.y ⟨x.1, x.2.2⟩))
  refine ⟨u, hu, fun p _ z hz hzu => ?_⟩
  obtain ⟨A, ev, hBA, hQ, hev⟩ := hA (PadicAlgCl p) z hz.1 hzu
  have hGood := hB A (fun x hx => hBA (by classical exact Finset.mem_coe.2 (Finset.mem_union_left _ hx))) hQ
  have hrat : ∀ (k : RM.K) (i j : RM.ι k), RM.y ⟨k, j⟩ ≠ 0 → RM.y ⟨k, i⟩ / RM.y ⟨k, j⟩ ∈ A := fun k i j _ =>
    hBA (by classical exact Finset.mem_coe.2 (Finset.mem_union_right _ (Finset.mem_image.2 ⟨⟨k, i, j⟩, Finset.mem_univ _, rfl⟩)))
  obtain ⟨la, T, io, e', y, evT, zT, t, hI⟩ :=
    GlobalTheory.T.root_origin_generic_frame_bound E H Dw l Xo c O β Y SS RM Sys Fx Or Fr hL.intAll hUn A p z ev hz hev hGood
  obtain ⟨hp, ho, hy, ⟨τ, hτ⟩, -⟩ := id hI
  let x : (Ref.pjSys Xo c).Pt la := (show Ref.PtU Xo c la from PtV.mk la ho y hy τ hτ)
  have hval : ∀ f, (Ref.pjSys Xo c).val x f = nval T.V e' (evI y f) :=
    fun f => Ref.pjSys_val_mk Xo c la ho y hy τ hτ f
  have hS := GlobalTheory.T.root_origin_frame_section_bound E H Dw l Xo c O β Y SS RM Sys Fx Or Fr A p z ev hz hev la T io e' y evT zT t hI x hval
  have hR := GlobalTheory.T.root_origin_frame_degree_bound hG E H Dw l Xo c O β Y SS RM Sys Fx Or Fr hOm hram A p z ev hz hev hGood hrat la T io e' y evT zT t hI
  obtain ⟨rec, h1, h2⟩ := FinRd.read_of_reads hz.1 x (FinRd.tOf_pos la T e' t) hS hR
  refine ⟨la, x, rec, hp, FinRd.val_indicator hL Rd hz.1 (FinRd.ram_pos hp) x hS, fun r' => ⟨(h1 r').1, ?_⟩, h2⟩
  rw [← latExp_eq]
  exact (h1 r').2

end GlobalTheory.CompanionTheory.Ar.Rec
