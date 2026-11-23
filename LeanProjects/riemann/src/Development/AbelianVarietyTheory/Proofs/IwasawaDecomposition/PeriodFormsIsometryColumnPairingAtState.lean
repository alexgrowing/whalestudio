import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowsAre
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIsBIffCoreB
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntegralFormsHermLatticeGoodAndComplexBasisStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormAtSqIntegralFormEqClassSumMetricStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowFormMetricEqClassSumMetricStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ClassSumComplexRowFormColumnsLevelEqStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

noncomputable section
namespace GlobalTheory.Mem.R3.Rw.EmtTw
attribute [local instance] GlobalTheory.Mem.Col2.starE
set_option maxHeartbeats 2000000

theorem inner_per_e {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} (P : Pre2 K w) (a : w.C.Tup)
    (y y' : Df.MtCx w.I a) : inner ℂ (P.q.per.e a y) (P.q.per.e a y') = Df.cSum w.I P.hX a y y' := by
  let jA := (P.q.t.tA true a).j
  have hF := (P.q.t.tA true a).forms
  let eS : (P.q.p.sA true a).A.T →ₗ[ℂ] Df.MtCx w.I a := (P.q.per.e a).symm.toLinearMap
  let j' := eS.comp jA
  have hspan : Submodule.span ℂ (Set.range j') = ⊤ := by
    have h0 : Submodule.span ℂ (Set.range jA) = ⊤ := by
      rw [← ColTie.span_single_eq]; exact hF.span
    have h1 : Set.range j' = eS '' Set.range jA := by
      rw [← Set.range_comp]; rfl
    rw [h1, Submodule.span_image, h0, Submodule.map_top]
    exact LinearMap.range_eq_top.2 (P.q.per.e a).symm.surjective
  obtain ⟨k, hk⟩ := Df.exists_embLL_im_ne (B := B) P.hX
  refine Df.inner_eq_of_norm_sq _ j' hspan k hk (P.q.per.e a).toLinearMap (Df.cSum w.I P.hX a) (fun m => ?_) y y'
  obtain ⟨x, hx, hjx⟩ := P.q.per.crd a m
  have hj' : j' m = Df.toCx w.I P.hX a x := by
    show (P.q.per.e a).symm (jA m) = _
    rw [show jA m = _ from hjx, LinearEquiv.symm_apply_apply]
  have he : (P.q.per.e a).toLinearMap (j' m) = jA m := by
    show (P.q.per.e a) ((P.q.per.e a).symm (jA m)) = _
    rw [LinearEquiv.apply_symm_apply]
  have hL := GlobalTheory.T.classSum_complexRowForm_columnsLevel_eq (w.st P.Z₀) w.I P.hX P.z.Xg P.z.tr a m x hx
  have hI := hF.inner m m
  rw [he, hj', hL]
  calc ((‖jA m‖ ^ 2 : ℝ) : ℂ) = inner ℂ (jA m) (jA m) := by rw [inner_self_eq_norm_sq_to_K]; norm_cast
    _ = _ := hI

theorem eMtTw_isometry_state : ∀ (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), K.Over B.toPre → Forced K B T →
    pinAnd HasPk K B f T w → ∀ (P : Pre2 K w) (x : St P) (hη : ∀ j v, 1 ≤ j → j ≤ B.R.m → x.o.η j v = P.q.eta j v), ∀ u (a : (w.D x.o.Z).what₂.Tup), a ≠ (w.D x.o.Z).what₂.mu0 → ∀ F G,
      inner ℂ ((w.D x.o.Z).eMtTw u a F) ((w.D x.o.Z).eMtTw u a G) = TC.ipMt w.I w.l u a F G := by
  intro K B f T w _ _ _ P x _ u a _ F G
  change inner ℂ (P.q.e.eT u a F) (P.q.e.eT u a G) = _
  have key : ∀ F : (TC.per w.I w.l u a).Mt, Df.SameForm w.I w.l u a ((P.q.per.e a).symm (P.q.e.eT u a F)) F := fun F => by
    have h := P.q.per.tw u a ((P.q.per.e a).symm (P.q.e.eT u a F))
    rw [LinearEquiv.apply_symm_apply] at h
    exact (congrArg (Df.SameForm w.I w.l u a ((P.q.per.e a).symm (P.q.e.eT u a F))) ((P.q.e.eT u a).symm_apply_apply F)).mp h
  have h1 : ∀ F : (TC.per w.I w.l u a).Mt, P.q.e.eT u a F = P.q.per.e a ((P.q.per.e a).symm (P.q.e.eT u a F)) := fun F =>
    ((P.q.per.e a).apply_symm_apply _).symm
  rw [h1 F, h1 G, inner_per_e P a, GlobalTheory.T.rowFormMetric_eq_classSumMetric w.I w.ok w.pins w.l P.hX x.o.Z u a F G _ _ (key F) (key G)]

end GlobalTheory.Mem.R3.Rw.EmtTw

end
