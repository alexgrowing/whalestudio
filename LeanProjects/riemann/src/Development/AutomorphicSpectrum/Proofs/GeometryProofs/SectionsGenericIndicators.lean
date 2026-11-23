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
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.EvaluationLawsGenericFramesAtlasHold
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLocalRingTrivSqZeroExt
import Formalism.LocalToGlobal.ProjectiveLattices.CompFin
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Rec

section GenInj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem allWt_eq_zero_of_generic (h : GenFrEx Xo c) {e : Ix Dw → ℤ} {g : Rul Xo c}
    (hg : g ∈ GlobalTheory.AllWt.secZ Xo c e) (h0 : ∀ Z, evC h Z g = 0) : g = 0 := by
  obtain ⟨hL, -, -, hA'⟩ := GlobalTheory.Reg.evLaws_genFr_atlas E H Dw l Xo c
  have hA := hA' h
  have hfield : ∀ (L : Type) [Field L] [Algebra c.F L] (w : FrPt Xo c L), evR Xo c g w = 0 := by
    intro L _ _ w
    obtain ⟨C, ψ, z, t', hz, hb⟩ := hA L w
    obtain ⟨q, χ, y₀, hy₀⟩ := hL.test C.R C.y
    have h1 : evR Xo c g C.yg = 0 := by
      rw [GlobalTheory.FlagTan.evR_frBor hg C.bor]
      have := h0 C.Z
      unfold evC at this
      rw [this, mul_zero]
    have h2 : χ (g q y₀) = 0 := by
      rw [GlobalTheory.FlagTan.evR_eq hg.1 (frMap_trans _ _ _ _ _ _ _ _ hy₀ C.gen)] at h1
      exact Subtype.ext h1
    have h3 : evR Xo c g z = 0 := by
      rw [GlobalTheory.FlagTan.evR_eq hg.1 (frMap_trans _ _ _ _ _ _ _ _ hy₀ hz), AlgHom.comp_apply, h2, map_zero]
    rw [GlobalTheory.FlagTan.evR_frBor hg hb, h3, mul_zero]
  funext p y
  have hred : IsReduced p.R := (Ideal.isRadical_iff_quotient_reduced _).1 p.rad
  show g p y = 0
  refine IsNilpotent.eq_zero ?_
  rw [nilpotent_iff_mem_prime]
  intro P hP
  let φ : p.R →ₐ[c.F] P.ResidueField := IsScalarTower.toAlgHom c.F p.R P.ResidueField
  obtain ⟨w, hw⟩ := hL.bc _ _ φ y
  have h4 := hfield _ w
  rw [GlobalTheory.FlagTan.evR_eq hg.1 hw] at h4
  exact Ideal.algebraMap_residueField_eq_zero.1 h4

theorem mem_allWt_of_secZ {a : WZ E} {f : Rul Xo c} (hf : f ∈ GlobalTheory.CompanionTheory.Ar.Rec.secZ Xo c a) :
    f ∈ GlobalTheory.AllWt.secZ Xo c (GlobalTheory.CompanionTheory.Ar.Rec.exZ Dw a) := by
  refine ⟨hf.1, fun p t y y' hb => ?_⟩
  rw [hf.2 p t y y' hb, Units.coe_prod]

theorem mem_secZ_of_allWt {a : WZ E} {f : Rul Xo c} (hf : f ∈ GlobalTheory.AllWt.secZ Xo c (GlobalTheory.CompanionTheory.Ar.Rec.exZ Dw a)) :
    f ∈ GlobalTheory.CompanionTheory.Ar.Rec.secZ Xo c a := by
  refine ⟨hf.1, fun p t y y' hb => ?_⟩
  rw [hf.2 p t y y' hb, Units.coe_prod]

theorem exZ_add (a b : WZ E) :
    GlobalTheory.CompanionTheory.Ar.Rec.exZ Dw (a + b) = GlobalTheory.CompanionTheory.Ar.Rec.exZ Dw a + GlobalTheory.CompanionTheory.Ar.Rec.exZ Dw b := by
  funext i
  cases i <;> simp [GlobalTheory.CompanionTheory.Ar.Rec.exZ]

theorem secZ_eq_zero_of_generic (h : GenFrEx Xo c) {a : WZ E} {f : Rul Xo c}
    (hf : f ∈ GlobalTheory.CompanionTheory.Ar.Rec.secZ Xo c a) (h0 : ∀ Z, evC h Z f = 0) : f = 0 :=
  allWt_eq_zero_of_generic h (mem_allWt_of_secZ hf) h0

theorem secZ_mul {a b : WZ E} {f g : Rul Xo c} (hf : f ∈ GlobalTheory.CompanionTheory.Ar.Rec.secZ Xo c a)
    (hg : g ∈ GlobalTheory.CompanionTheory.Ar.Rec.secZ Xo c b) : f * g ∈ GlobalTheory.CompanionTheory.Ar.Rec.secZ Xo c (a + b) := by
  apply mem_secZ_of_allWt
  rw [exZ_add]
  exact GlobalTheory.AllWt.mul_mem_secZ (mem_allWt_of_secZ hf) (mem_allWt_of_secZ hg)

theorem one_mem_secZ_zero : (1 : Rul Xo c) ∈ GlobalTheory.CompanionTheory.Ar.Rec.secZ Xo c (0 : WZ E) :=
  ⟨fun p q φ y z _ => by simp, fun p t y y' _ => by simp [GlobalTheory.CompanionTheory.Ar.Rec.exZ]⟩

theorem evC_mul_of_test {h : GenFrEx Xo c} (hT : GenFromTest Xo c h) (Z : Comp Xo c) (f g : Rul Xo c) :
    evC h Z (f * g) = evC h Z f * evC h Z g := by
  unfold evC evR evalAt
  rw [dif_pos (hT Z), dif_pos (hT Z), dif_pos (hT Z)]
  exact map_mul _ _ _

theorem evC_one_of_test {h : GenFrEx Xo c} (hT : GenFromTest Xo c h) (Z : Comp Xo c) :
    evC h Z (1 : Rul Xo c) = 1 := by
  unfold evC evR evalAt
  rw [dif_pos (hT Z)]
  exact map_one _

end GenInj

theorem sections_generic_indicators : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (h : GenFrEx Xo c) (e : Comp Xo c → Rul Xo c), CompLaws U h e → (∀ a, ∀ f ∈ secZ Xo c a, (∀ Z, evC h Z f = 0) → f = 0) ∧ (∀ a Z, ∀ f ∈ cuspOn U h a Z, evC h Z f = 0 → f = 0) ∧ (∀ a b, ∀ f ∈ secZ Xo c a, ∀ g ∈ secZ Xo c b, f * g ∈ secZ Xo c (a + b)) ∧ (∀ Z, e Z * e Z = e Z) ∧ (∀ Z Z', Z ≠ Z' → e Z * e Z' = 0) ∧ ∑ᶠ Z, e Z = 1 := by
  intro E _ _ _ H Dw l Xo c r U h e hC
  have hT := hC.genT
  have hz : ∀ Z, e Z ∈ GlobalTheory.CompanionTheory.Ar.Rec.secZ Xo c (0 : WZ E) := fun Z => by
    have h1 := hC.e_sec Z
    rw [← GlobalTheory.CompanionTheory.Ar.Rec.secZ_nat] at h1
    have h2 : (fun x => ((((0 : (E →+* ℂ) × ℕ → ℕ)) x : ℕ) : ℤ)) = (0 : WZ E) := by
      funext x
      simp
    rwa [h2] at h1
  have hmul : ∀ {f g : Rul Xo c}, f ∈ GlobalTheory.CompanionTheory.Ar.Rec.secZ Xo c (0 : WZ E) →
      g ∈ GlobalTheory.CompanionTheory.Ar.Rec.secZ Xo c (0 : WZ E) → f * g ∈ GlobalTheory.CompanionTheory.Ar.Rec.secZ Xo c (0 : WZ E) := by
    intro f g hf hg
    have := secZ_mul hf hg
    rwa [add_zero] at this
  have heq : ∀ {f g : Rul Xo c}, f ∈ GlobalTheory.CompanionTheory.Ar.Rec.secZ Xo c (0 : WZ E) →
      g ∈ GlobalTheory.CompanionTheory.Ar.Rec.secZ Xo c (0 : WZ E) → (∀ Z, evC h Z f = evC h Z g) → f = g := by
    intro f g hf hg hv
    refine sub_eq_zero.1 (secZ_eq_zero_of_generic h (Submodule.sub_mem _ hf hg) fun Z => ?_)
    rw [← evL_apply, map_sub, evL_apply, evL_apply, hv Z, sub_self]
  have hfin : Finite (Comp Xo c) := Formalism.L2.Pj.CompFin.finite_comp Xo c
  letI := Fintype.ofFinite (Comp Xo c)
  classical
  refine ⟨fun a f hf h0 => secZ_eq_zero_of_generic h hf h0, fun a Z f hf h0 => ?_,
    fun a b f hf g hg => secZ_mul hf hg, fun Z => ?_, fun Z Z' hne => ?_, ?_⟩
  · obtain ⟨h1, h2⟩ := Submodule.mem_inf.1 hf
    refine secZ_eq_zero_of_generic h (Submodule.mem_inf.1 h1).1 fun Z' => ?_
    by_cases hZ : Z' = Z
    · rw [hZ]
      exact h0
    · have h3 := Submodule.mem_iInf _ |>.1 h2 Z'
      have h4 := Submodule.mem_iInf _ |>.1 h3 hZ
      exact h4
  · refine heq (hmul (hz Z) (hz Z)) (hz Z) fun Z' => ?_
    rw [evC_mul_of_test hT]
    by_cases hZ : Z' = Z
    · subst hZ
      rw [(hC.e_val Z').1, one_mul]
    · rw [(hC.e_val Z).2 Z' hZ, zero_mul]
  · refine heq (hmul (hz Z) (hz Z')) (Submodule.zero_mem _) fun Y => ?_
    have hzero : evC h Y (0 : Rul Xo c) = 0 := by
      rw [← evL_apply, map_zero]
    rw [evC_mul_of_test hT, hzero]
    by_cases hY : Y = Z
    · subst hY
      rw [(hC.e_val Z').2 Y hne, mul_zero]
    · rw [(hC.e_val Z).2 Y hY, zero_mul]
  · rw [finsum_eq_sum_of_fintype]
    refine heq (Submodule.sum_mem _ fun Z _ => hz Z) one_mem_secZ_zero fun Y => ?_
    rw [evC_one_of_test hT, ← evL_apply, map_sum, Finset.sum_eq_single Y]
    · rw [evL_apply]
      exact (hC.e_val Y).1
    · intro Z _ hZ
      rw [evL_apply]
      exact (hC.e_val Z).2 Y (Ne.symm hZ)
    · intro hY
      exact absurd (Finset.mem_univ Y) hY

end GlobalTheory.CompanionTheory.Ar.Rec
