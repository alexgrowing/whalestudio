import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNewTwistLamFullStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PublishedInputsThirdLayer
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SameGaloisLevelExists
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HeckeOpen
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RootsOfUnityRingLeWittIntegers
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FactsStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ThetaLocalInputs
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SeriesStateB1OfGeometry
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec

set_option synthInstance.maxHeartbeats 200000

section
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.StandardLattice Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie GlobalTheory.ExportSeries NumberField IsDedekindDomain
open Formalism.MainNotions.IntegralHeckeForms (TwOK HkIdx)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting.Up GlobalTheory.Mem.R3.Tr
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 4000000
namespace GlobalTheory.HeightCounting.SerCopy
variable {K : Ctx} {B : GlobalTheory.Mem.Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w}
section Install
variable {x : St P} {N₁ : TwNew (Dof x)} {kKs : (datTw x N₁).core.Q.c.F →+* ↥(DN x N₁).LL0}
  {hk : ∀ y, ((kKs y : ↥(DN x N₁).LL0) : (DN x N₁).what₂.LL) = algebraMap (datTw x N₁).core.Q.c.F (DN x N₁).what₂.LL y}
  {cf : CharFrame (DN x N₁)} {Rw : RowSide (DN x N₁)}
  {Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield (DN x N₁).host.E)) → PlE (DN x N₁).host} {hf eig θ}
  {Bs : SideB (DN x N₁) cf Rw (lowAll (DN x N₁)) Pq (ratDatR (datTw x N₁).R (datTw x N₁).cG kKs hk) hf eig θ} {hF}
  (p : PreTie (ysOf Bs) (datTw x N₁).geo.v₀ Bs.exp hF Pq)
end Install
open GlobalTheory.Mem.Top.GroupRetwisting in
theorem series_copy_embedding_alt : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → SerN → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T}, K.Over B.toPre → Forced K B T → Start K B f T w → ∀ {P : Pre2 K w} (x : St P) (l : _root_.GlobalTheory.HeightCounting.Up.FirstIntermediateLevel hL x), ∃ N : TwNew (Dof x), (∀ Z : GlobalTheory.LamTie.LamDat (Dof x), GlobalTheory.LamTie.IsLamTieFull (Dof x).ntw Z → GlobalTheory.LamTie.IsLamTieFull N.tw Z) ∧ ∀ (x' : St P) (l' : _root_.GlobalTheory.HeightCounting.Up.IntermediateLevel hL x'), x'.o = oTw x N → HEq l'.a.A.row (N.row l.a.A.row) → HEq l'.Pq l.Pq → HEq l'.rat.S (N.rat l.rat.S) → HEq l'.rat.In.Sb l.rat.In.Sb → HEq l'.rat.In.hL l.rat.In.hL → HEq l'.rat.In.eig l.rat.In.eig → HEq l'.rat.In.θ l.rat.In.θ → HEq x'.m.z.R (GlobalTheory.Mem.R3.Tr.real3 (a := x.o.Z) (oTw x N).Z (iK := x.m.z.alg) x.m.z.R) → HEq x'.m.z.cG x.m.z.cG → HEq x'.m.z.geo (GlobalTheory.Mem.R3.Tr.geoHalf (a := x.o.Z) (oTw x N).Z (iK := x.m.z.alg) x.m.z.geo) → ∀ m : InMt x'.r.Y (cfOf x') w.I.xi (QOf P), (∀ i, GlobalTheory.MtRead.IdFrame x'.r.Y.hF (m.ad.PV i)) → Nonempty (_root_.GlobalTheory.HeightCounting.SeriesData x'.m.z.geo l'.a l'.rat m.ad.PV l'.Pq) := by
  intro hPr _ hL K B f T w hK _ hS P x l
  obtain ⟨-, -, -, -, hr⟩ := _root_.GlobalTheory.T.isChoice_of_start_of_over hL hK hS x l.toLA
  obtain ⟨N, h1, h2, h3, h4, hB⟩ := exists_prepared hPr.what₂.art l.b.Bs l.a.val hr
  obtain ⟨Z, z1, z2, z3, z4, z5⟩ := l.b.lam
  have hSb : ∀ i, l.rat.In.Sb ⊆ N.tw.S0 i := fun i => by
    obtain ⟨i₀, e, -⟩ := h2 i
    rewrite [e]
    exact l.b.Sb_le i₀
  have hS0 : ∀ i, OverSet (Dof x) (N.tw.S0 i) (insert (N.tw.l i) (lowAll (Dof x))) := fun i => by
    obtain ⟨i₀, e, e'⟩ := h2 i
    rewrite [e, e']
    exact l.b.rootsOfUnityRing_le_wittIntegers i₀
  obtain ⟨hC, kKs, hk, hf, g, Bs, hF, hτ, ⟨p⟩⟩ := _root_.GlobalTheory.HeightCounting.SerCopy.pre_at_twisted_copy_of_side_b_tau_true hPr.what₂.art hK hS x l.toLI N hB hSb
    ⟨_, (lamT_spec N ⟨z1, z2, z3, z4, h1 Z z5⟩).1⟩
  refine ⟨nP p, h1, fun x' l' ho hrow hPq _ hSb' hhL heig hθ hR hcG hgeo m hm => ?_⟩
  obtain ⟨o', fits', G_eq', etaF', bk', m', copy', coh', s', r', pin'⟩ := x'
  dsimp only at ho
  subst ho
  have e4 : l'.rat.In.Sb = (by with_unfolding_all exact (l.rat.In.Sb :)) := (by with_unfolding_all exact ((eq_of_heq hSb') :))
  exact _root_.GlobalTheory.HeightCounting.SerCopy.series_state_b1_twist_alt p hτ hC ((by with_unfolding_all exact (h4 :))) ((by with_unfolding_all exact (h3 :))) m'.z (moved_eq_datTw x _ m' copy' hR hcG hgeo) r'.Y l'.a l'.rat m.ad.PV hm l'.Pq
    ⟨(by with_unfolding_all exact ((lamT (nP p) Z) :)), (by with_unfolding_all exact ((lamT_spec (nP p) ⟨z1, z2, z3, z4, h1 Z z5⟩) :))⟩ ((by with_unfolding_all exact (hrow :))) ((by with_unfolding_all exact (hPq :))) (hhL.trans g.symm) ((by with_unfolding_all exact (heig :))) ((by with_unfolding_all exact (hθ :)))
    (by rewrite [e4]; exact (by with_unfolding_all exact (hSb :))) ((by with_unfolding_all exact (hS0 :)))
end GlobalTheory.HeightCounting.SerCopy
end
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.series_copy_embedding_of_cmDatum_alt : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → SerN → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T}, K.Over B.toPre → Forced K B T → Start K B f T w → ∀ {P : Pre2 K w} (x : St P) (l : _root_.GlobalTheory.HeightCounting.Up.FirstIntermediateLevel hL x), ∃ N : TwNew (Dof x), (∀ Z : GlobalTheory.LamTie.LamDat (Dof x), GlobalTheory.LamTie.IsLamTieFull (Dof x).ntw Z → GlobalTheory.LamTie.IsLamTieFull N.tw Z) ∧ ∀ (x' : St P) (l' : _root_.GlobalTheory.HeightCounting.Up.IntermediateLevel hL x'), x'.o = oTw x N → HEq l'.a.A.row (N.row l.a.A.row) → HEq l'.Pq l.Pq → HEq l'.rat.S (N.rat l.rat.S) → HEq l'.rat.In.Sb l.rat.In.Sb → HEq l'.rat.In.hL l.rat.In.hL → HEq l'.rat.In.eig l.rat.In.eig → HEq l'.rat.In.θ l.rat.In.θ → HEq x'.m.z.R (GlobalTheory.Mem.R3.Tr.real3 (a := x.o.Z) (oTw x N).Z (iK := x.m.z.alg) x.m.z.R) → HEq x'.m.z.cG x.m.z.cG → HEq x'.m.z.geo (GlobalTheory.Mem.R3.Tr.geoHalf (a := x.o.Z) (oTw x N).Z (iK := x.m.z.alg) x.m.z.geo) → ∀ m : InMt x'.r.Y (cfOf x') w.I.xi (QOf P), (∀ i, GlobalTheory.MtRead.IdFrame x'.r.Y.hF (m.ad.PV i)) → Nonempty (_root_.GlobalTheory.HeightCounting.SeriesData x'.m.z.geo l'.a l'.rat m.ad.PV l'.Pq) := by
  first | exact @_root_.GlobalTheory.HeightCounting.SerCopy.series_copy_embedding_alt | exact _root_.GlobalTheory.HeightCounting.SerCopy.series_copy_embedding_alt | (intros; apply _root_.GlobalTheory.HeightCounting.SerCopy.series_copy_embedding_alt <;> assumption)
end
end
