import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.DepthZeroSupport
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BoundAtTwoThreeFamily
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.GeometricWeakTiesOfStrong
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GKeyFin
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnlocalizedSaturatedState
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GeometricConditionLargeGridStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventualFunctionGridLarge
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventualRowsOfClassSums
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RowOfCovolumeOntoGrid
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.Mem.LiteralAutomorphy

namespace GlobalTheory.Fc.StageOne

theorem rowFun_at_gridA : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → GlobalTheory.NT.RayField → GlobalTheory.BigTop.Fun.Fun0Fit @GlobalTheory.BigTop.Fun.Fld → ∃ CF0 : ℝ, ∀ CF, CF0 ≤ CF → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (N : NExt hL) (S : SExt) (Γ : GeoP), (∀ K B f T w Z Wt p0 t nch n xd c, N K B f T w Z Wt p0 t nch n xd c → Nonempty (GlobalTheory.HeightCounting.Up.NEl hL CF K B f T w Z Wt p0 t nch n xd c)) → S0.Open0 (prmR (NEa hL N (GridA CF)) S Γ) → RL.At (prmR (NEa hL N (GridA CF)) S Γ) S0.FunctorialityCondition := by
  intro hDS hHC hCR hCW hRay hFun
  obtain ⟨CF0, hCF⟩ := GlobalTheory.Fc.Ind.evWC_fun_of_fun0Fit @GlobalTheory.BigTop.Fun.Fld hFun
  refine ⟨CF0, fun CF hle hL N S Γ hN o => ?_⟩
  have hA := GlobalTheory.T.geometric_condition_large_grid hRay hL CF N S Γ hN o.hDivG o.tie
  obtain ⟨R, hR, h⟩ := RowL.and (RowL.and (RowL.and o.hPA o.hDivG) o.good) hA
  refine ⟨R, hR, h.imp fun 𝒜 σ hsel H => ?_⟩
  obtain ⟨⟨⟨hpa, hdv⟩, hgd⟩, hgeo⟩ := H
  choose τ hτ using fun {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) x hx i => hgeo Fm hc x hx i
  let τ' : TieSel σ := fun Fm hc x hx i => τ Fm hc x hx i
  have hduty : ∀ (eps : ℝ) (Fm : FamP eps), 𝒜 Fm → GlobalTheory.EX.DQ.Duty7 Fm := fun _ Fm hc =>
    let ⟨_, _, h7, _⟩ := hsel Fm hc
    (DQ.familyClass_sevenDuties_and_stableLattices _ Fm h7).1
  have hrows : Ind.EvW Ind.PRows 𝒜 (partSel σ τ') :=
    GlobalTheory.Fc.Ind.evW_pRows_of_rows hDS hHC hCR hCW 𝒜 (partSel σ τ') (fun Fm hc x hx i => hpa Fm hc x hx i)
      (fun Fm hc x hx i => GlobalTheory.Fc.FourBoundsAtBundles.pDiv_of _ (hdv Fm hc x hx i)) hgd
      (fun Fm hc x hx i => ⟨(hτ Fm hc x hx i).2.1, (hτ Fm hc x hx i).2.2.1⟩)
  have key := hCF CF hle 𝒜 (partSel σ τ') hduty hrows
    (GlobalTheory.Fc.FourBoundsAtBundles.evW_of_atAll fun Fm hc x hx i => (hτ Fm hc x hx i).2.2.2.2.2)
  first | exact key | exact ⟨τ', key⟩

end GlobalTheory.Fc.StageOne
