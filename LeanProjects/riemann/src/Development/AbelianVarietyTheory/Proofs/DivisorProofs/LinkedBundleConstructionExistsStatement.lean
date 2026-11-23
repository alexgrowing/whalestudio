import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinkedBundleConstructionExists
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.BhattScholzeCrystallineLattices
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.DepthZeroSupport
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BoundAtTwoThreeFamily
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.GeometricWeakTiesOfStrong
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GKeyFin
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnlocalizedSaturatedState
import Development.AbelianVarietyTheory.Definitions.Divisors.HypothesisBundleConversions
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.Mem.LiteralAutomorphy
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linked_bundle_construction_exists : S0.HypothesesUE → S0.RowRat → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (cDep : ℝ) (A : GroupRetwisting.AtP), EvLgG A → StandardLattice.SiegelMassRatioCM ∧ MemberE (prmR (NEa hL (GlobalTheory.HeightCounting.Up.NEo hL cDep) A) SExt.none (geoCl anyGeometry)).s ∧ ExBL KPx (IsBuiltE (prmR (NEa hL (GlobalTheory.HeightCounting.Up.NEo hL cDep) A) SExt.none (geoCl anyGeometry)).s) (IsGoodE (prmR (NEa hL (GlobalTheory.HeightCounting.Up.NEo hL cDep) A) SExt.none (geoCl anyGeometry)).s) (IsLinked (prmR (NEa hL (GlobalTheory.HeightCounting.Up.NEo hL cDep) A) SExt.none (geoCl anyGeometry))) := by
  first | exact @GlobalTheory.Fc.StageOneU.member_bundles_large_ue | exact GlobalTheory.Fc.StageOneU.member_bundles_large_ue | (intros; apply GlobalTheory.Fc.StageOneU.member_bundles_large_ue <;> assumption)
