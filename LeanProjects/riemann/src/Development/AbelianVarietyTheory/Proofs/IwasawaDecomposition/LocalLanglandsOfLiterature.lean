import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Brauer
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.HypothesesX
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SeriesRatSOf
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenUsedOfCenReal
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ExistsIdealsPrimeToEqSpan
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RhoMemOfMkEq
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChebotarevDegreeOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SumRangeEqRoots
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivOfIsSubquotient
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PublishedInputsCombinedStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DepthZeroInertiaOfLanglandsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalLanglandsOfPublishedStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DiscreteSpectrumOfResidualStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GenericUnitaryDualGlStatement

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.Mem.LiteralAutomorphy

namespace GlobalTheory.Mem.LiteralAutomorphy

theorem localLanglandsGL_and_prN_of_lit : LitLoc → LitAut → GlobalTheory.Published.LocalLanglandsGL ∧ PrN := by
  intro L A
  have hL : GlobalTheory.Published.LocalLanglandsGL :=
    GlobalTheory.T.local_langlands_of_published L.llc L.conv L.dzc L.dzi L.brauer L.chev A.art L.exh L.multi L.cos L.zel L.geo L.bz
  refine ⟨hL, ?_⟩
  have hG : GlobalTheory.GLq.Green := GlobalTheory.GreenBridge.green_of_regular L.green
  exact
    { what₂ := GlobalTheory.T.published_inputs_combined L.bz L.bern L.geo L.disj L.mp L.theta A.js A.fin A.ctemp L.temp L.seg A.gk A.gal A.car
        A.pur A.coh A.art A.chA A.chW A.berger GlobalTheory.Published.chebotarevDegreeOne' hL
      decay := A.decay
      hc := A.hc
      greenC := hG
      green := hG
      zel := L.zel
      dz := GlobalTheory.T.depth_zero_inertia_of_langlands L.dzt A.art hL
      ray := A.ray
      rayF := A.ray
      rayA := GlobalTheory.Published.GlobalArtinReciprocity.rayCharacterArtin A.art
      bc := GlobalTheory.BaseChangeBridge.main A.bc L.bern
      ds := GlobalTheory.T.discrete_spectrum_of_residual A.mw
      gen := GlobalTheory.T.generic_unitary_dual_gl L.unit L.sq L.gen L.multi L.cos
      std := L.cos
      cheb := GlobalTheory.Published.cheb_holds
      howe := GlobalTheory.Hk3.howeUnram_holds }

end GlobalTheory.Mem.LiteralAutomorphy
