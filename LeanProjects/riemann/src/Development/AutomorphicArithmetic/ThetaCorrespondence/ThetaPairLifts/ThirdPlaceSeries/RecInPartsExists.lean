import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SelectedRealizationSide
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NormChoiceOfExtension
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CoreAltAltBis
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SameGaloisLevelExists
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LayerTwoFamilyClass
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LinkedFamiliesFixedValues
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LinkedFamiliesKernelFrame
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TwistedBundle
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealRecOf
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ToSTiesR
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealRec
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MjReadRealizationEqual
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RingSpecNormalisedCharacterEqAlt
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GoodGenericRowsStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ScalRowsStatement
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up GlobalTheory.Mem.SRe GlobalTheory.Mem.R3.Rw
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Lev
open GlobalTheory.Mem.R3
noncomputable section
namespace GlobalTheory.Mem.R3.RecInAt
set_option maxHeartbeats 4000000 in
theorem recIn_parts_exists_alt : GlobalTheory.Published.GreenCuspidal → GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.NT.RayField → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (N : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL) (Γ : GeoP) (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL), p = _root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N SExt.none Γ → (∀ K B f T w Z Wt p0 t nch n xd c, N K B f T w Z Wt p0 t nch n xd c → Nonempty (_root_.GlobalTheory.HeightCounting.Up.extensionWithLaw hL K B f T w Z Wt p0 t nch n xd c)) → ∀ (K : Ctx) (q : WPt p.s K), (∀ X : GlobalTheory.Mem.Stages, K.Over X.B.toPre → HostHyp X.toD7 ∧ X.toD7.host.F = maximalRealSubfield X.toD7.host.E ∧ (∀ i, IsFDiag (Wc X.toD7 i) ∧ IsFDiag (Vc X.toD7 i)) ∧ (∀ i, (Vc X.toD7 i).IsPosDef) ∧ (∀ j, Formalism.IndefR.Seed.FrmC.StdLat (X.toD7.sp.Y j) ∧ Formalism.IndefR.Seed.FrmC.StdLat (X.toD7.sp.V j) ∧ (1 ≤ j → j ≤ X.toD7.R.m → Formalism.IndefR.Seed.FrmC.StdLat (X.toD7.sp.W j))) ∧ Formalism.IndefR.Seed.FrmC.StdLat X.toD7.sp.X' ∧ (∀ i, (∀ a b, (Vc X.toD7 i).hT ((Vc X.toD7 i).frame a) ((Vc X.toD7 i).frame b) = if a = b then 1 else 0) ∧ (Vc X.toD7 i).L0 = Submodule.span (𝓞 X.toD7.host.E) (Set.range (Vc X.toD7 i).frame)) ∧ ((∀ a b, X.toD7.sp.X'.hT (X.toD7.sp.X'.frame a) (X.toD7.sp.X'.frame b) = if a = b then 1 else 0) ∧ X.toD7.sp.X'.L0 = Submodule.span (𝓞 X.toD7.host.E) (Set.range X.toD7.sp.X'.frame))) → GlobalTheory.CuspMult.MultEq q.x.what₂.r.z.R.toRealDat → ∀ (R : _root_.Formalism.L2.RecTAlt q.O.ex), _root_.GlobalTheory.Mem.Top.Bl.RecordCompatibleExtended q R → ∀ (sP : GlobalTheory.Mem.SRe.SPack (q.w.D q.Z) fun u => (R.T.cols.forms u).to0) (sS : GlobalTheory.Mem.SRe.SRest sP), HEq sP q.saturationAtWeightedPoint.P → HEq sS q.saturationAtWeightedPoint.S → ∀ (a : TwArgs q.O.ex q.x.what₂) (x : TwIn q.O.ex), HEq a.x x → ∀ (y : _root_.GlobalTheory.Mem.R3.RealInAlt x R (sS.toRealSpectralMatching R)), ∃ r : _root_.GlobalTheory.Mem.R3.RecursiveInput y, (_root_.GlobalTheory.Mem.R3.realisationRecursionOfInput r).PartsRow := by
  intro hGC hDC hHM hCW hW hDS hHC hCR hGAR hRF hL N Γ p hp hN K q hH hM R hR sP sS hP hS a x hax y
  obtain rfl := eq_of_heq hax
  classical
  obtain ⟨hC, -, hxi, -⟩ := GlobalTheory.Mem.R3.twArgs_lev K q.B q.f q.T q.w q.Z q.x.Wt _ _ _ _ _ _ _ q.O.ex q.x.what₂ a
  have hmt := _root_.GlobalTheory.Mem.R3.Reads.mt_mj_read_alt _ _ _ _ _ _ _ _ q.O.ex a.x R (sS.toRealSpectralMatching R) y a.intersectionNumber_baseChange
  have hFr : Top.Fr.at (q.w.st q.Z) q.f = GlobalTheory.Mem.Col2.TC.cf q.w.I q.w.l q.Z :=
    (congrArg (Top.Fr.at (q.w.st q.Z)) q.w.C_eq.symm).trans rfl
  have hchr := hR.s.chr
  have hC' : a.x.R.C = R.T.n.cf := by
    have h1 := eq_of_heq hC
    rw [h1, hFr]
    exact (congrArg Sigma.fst hchr).symm
  have heig := @GlobalTheory.T.partsRow_of_eigensystemIndex_goodCharacters hW hDS hHC hCR _ a.x.G a.x.grp a.x.fin _ _ _ a.x.A3 _ _ _ a.x.alg a.x.R a.x.F a.x.cG q.O.ex.p0 a.x.Y a.x.Z q.O.X a.x.pins a.intersectionNumber_baseChange
  letI := a.x.grp
  letI := a.x.fin
  letI := a.x.alg
  have hHost : HostHyp (q.w.D q.Z) := (hH (q.w.st q.Z) q.x.isOver).1
  have hgen : ∀ χ ∈ a.x.A3.A.X, chiIdem χ * lvlIdem a.x.F.P0 a.x.F.ψ0 ≠ 0 :=
    _root_.GlobalTheory.T.geometric_parameter_of_reciprocity_alt hDC hHM hCW hW hDS hHC hCR hGAR hRF hL N Γ p hp hN K q hH hM a
  have hlam : ∀ (i : Fin (q.w.D q.Z).R.m) π (c : a.x.A3.fam3.base3.Ix) (e : (q.w.D q.Z).what₂.LL →+* ℂ),
      (q.w.D q.Z).what₂.isot ((i : ℕ) + 1) π ≠ ⊥ → (q.w.D q.Z).what₂.isot ((i : ℕ) + 1) π ≤ (a.x.R.Wp3 i c).comap (a.x.Y.mj.eW i) →
      q.O.X.logLam ((i : ℕ) + 1) π e = Real.log (a.x.R.lam3 i a.x.A3.A.μ0 c (InfinitePlace.mk e)) :=
    _root_.GlobalTheory.T.parameter_of_discrete_series_reciprocity_alt hGC hDC hHM hCW hW hDS hHC hCR hGAR hRF hL N Γ p hp hN K q hH hM a
  obtain ⟨E, labPi, piOf, hparts⟩ := heig hHost hgen hlam
  have key : ∀ (c : Formalism.L2.Host.CharFrame (q.w.D q.Z)) (h : R.T.n.cf = c),
      (cast (congrArg (fun c => Formalism.L2.Host.TupTied (q.w.D q.Z) c q.O.ex.nch) h) R.T.n.tp).xi = R.T.n.tp.xi := by
    intro c h; subst h; rfl
  have key2 : ∀ (c1 c2 : Formalism.L2.Host.CharFrame (q.w.D q.Z)) (t1 : Formalism.L2.Host.TupTied (q.w.D q.Z) c1 q.O.ex.nch)
      (t2 : Formalism.L2.Host.TupTied (q.w.D q.Z) c2 q.O.ex.nch), c1 = c2 → HEq t1 t2 → t1.xi = t2.xi := by
    intro c1 c2 t1 t2 h ht; subst h; cases ht; rfl
  obtain ⟨hcf, htp⟩ := Sigma.mk.inj_iff.1 hchr
  have hxiR : R.T.n.tp.xi = q.w.I.xi := (key2 _ _ _ _ hcf htp).trans q.x.n.xi
  have htx : ∀ μ, Formalism.IndefR.RecTie.Used0 (q.w.D q.Z) μ → a.x.R.toLevCh.xiH (a.x.Y.tupT μ) =
      (cast (congrArg (fun c => Formalism.L2.Host.TupTied (q.w.D q.Z) c q.O.ex.nch) hC'.symm) R.T.n.tp).xi μ := by
    intro μ hμ
    rw [key _ hC'.symm, hxiR]
    exact eq_of_heq (hxi μ hμ).2
  refine ⟨⟨E, labPi, piOf, cast (congrArg (fun c => Formalism.L2.Host.TupTied (q.w.D q.Z) c q.O.ex.nch) hC'.symm) R.T.n.tp, cast_heq _ _, htx, hmt.1, hmt.2⟩, ?_⟩
  exact hparts
end GlobalTheory.Mem.R3.RecInAt
end
end
