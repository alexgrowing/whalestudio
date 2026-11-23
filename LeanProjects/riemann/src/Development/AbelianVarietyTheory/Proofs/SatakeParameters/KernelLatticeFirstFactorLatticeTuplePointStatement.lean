import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelLatticeFirstFactorLatticeTuplePoint
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.LocSpBot
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaSeriesDataHypothesesBelowMaximalLevel
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsMidLevIff
import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.FrecAt
import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.MovDXiAtRecStep
import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.LocalClassDataOfTrivialStabilizers
import Formalism.LocalToGlobal.GlobalTheory.BaseLatticeSelfDual
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernelLatticeFirstFactor_latticeTuplePoint : ∀ {D : D7} {i : ℕ} {hi : i ≤ D.R.m} {T : ℕ} {bad : Set (HeightOneSpectrum (𝓞 D.host.F))} (lev : StepLevel D.host.F D.host.E (sigD D) (gramN D i hi) T D.R.f bad) {p : ℕ} {G : GAtP p} (A : LocAt D.host.F D.host.E (D.R.N i) G) (a : 𝓞 D.host.E), (∃ co, IsOrthCo (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D i hi) co) → SplAlg A → LocInt A → LbAtB A lev.Lb → 0 < T → ∀ (c : G.comp) (g : ∀ v, GL (Fin (G.P.m + 1)) (G.P.Qq v)) (x : UPts (sigD D) (gramN D i hi) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)), A.IsPt c g x.1 → ∀ v, IsUnit (T : G.P.W v) → locSp (G.P.W v) (A.iw v) (latK D.sp (gramN D i hi) a x.1 lev.Lb) = colSpan (G.P.W v) ((LinearMap.toMatrix' (stdCo (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D i hi)).toLinearMap * A.B.1).map (A.iw v) * (castGL A.rk (G.P.Qq v) (g v) : Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) (G.P.Qq v))) := by
  first | exact @GlobalTheory.TwV.KerSp.locSp_latK_isPt | exact GlobalTheory.TwV.KerSp.locSp_latK_isPt | (intros; apply GlobalTheory.TwV.KerSp.locSp_latK_isPt <;> assumption)
