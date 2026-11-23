import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.LocSpBot
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaSeriesDataHypothesesBelowMaximalLevel
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsMidLevIff
import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.FrecAt
import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.MovDXiAtRecStep
import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.LocalClassDataOfTrivialStabilizers
import Formalism.LocalToGlobal.GlobalTheory.BaseLatticeSelfDual
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocSpCompanEq
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SmulDualSetLatAdMem
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatAdLocOf
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocSpLatAdIsPt
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MapApplyEqMulVec
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.TwV.KerSp

theorem locSp_latK_isPt : ∀ {D : D7} {i : ℕ} {hi : i ≤ D.R.m} {T : ℕ} {bad : Set (HeightOneSpectrum (𝓞 D.host.F))} (lev : StepLevel D.host.F D.host.E (sigD D) (gramN D i hi) T D.R.f bad) {p : ℕ} {G : GAtP p} (A : LocAt D.host.F D.host.E (D.R.N i) G) (a : 𝓞 D.host.E), (∃ co, IsOrthCo (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D i hi) co) → SplAlg A → LocInt A → LbAtB A lev.Lb → 0 < T → ∀ (c : G.comp) (g : ∀ v, GL (Fin (G.P.m + 1)) (G.P.Qq v)) (x : UPts (sigD D) (gramN D i hi) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)), A.IsPt c g x.1 → ∀ v, IsUnit (T : G.P.W v) → locSp (G.P.W v) (A.iw v) (latK D.sp (gramN D i hi) a x.1 lev.Lb) = colSpan (G.P.W v) ((LinearMap.toMatrix' (stdCo (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D i hi)).toLinearMap * A.B.1).map (A.iw v) * (castGL A.rk (G.P.Qq v) (g v) : Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) (G.P.Qq v))) := by
  intro D i hi T bad lev p G A a hco hS hI hB hT c g x hx v hTv
  have hLb : Formalism.L2.GlobalTheoryTheory.Comp.IsLat lev.Lb := ⟨lev.Lb_fin, lev.Lb_span⟩
  have hdual := GlobalTheory.smul_dualSet_latAd_mem D.sp (gramN D i hi) hco T lev.Lb hT hLb lev.Lb_dual x.1 x.2
  have hLA : LatAdLoc A lev.Lb := GlobalTheory.TwV.latAdLoc_of A lev.Lb hS hI lev.Lb_fin lev.Lb_span
  unfold Formalism.MainNotions.G.KAat.latK Formalism.L2.PairingIndexBounds.F.toStd
  rw [GlobalTheory.TwV.locSp_map, GlobalTheory.TwV.CompSp.locSp_compan_eq D.sp (G.P.W v) (G.P.Qq v) (A.iw v) (gramN D i hi) a T _ hTv hdual,
    GlobalTheory.TwV.SpanPt.locSp_latAd_isPt A lev.Lb hLA hB c g x.1 hx v, GlobalTheory.TwV.SpanPt.colSpan_map]
  rw [Matrix.map_mul, Matrix.mul_assoc]
  rfl

end GlobalTheory.TwV.KerSp
