import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecondChernDensity
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToroidalChartBoundaryRegularStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundarySettingHeightLowerStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundarySettingHeightUpperStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundarySettingHeightComparisonStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory Matrix NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.ArInt GlobalTheory.CovTest GlobalTheory.VdmRec GlobalTheory.ArchLim
open GlobalTheory.MixDens (part IsDens chernMat emb)
open GlobalTheory.FlagFibre (Low uni)
open ReciprocityTheory.L2DbarEstimates (V cHess bas)
open ReciprocityTheory.AnForm.M (LocPot FinHolAtlas IsPotential IsSection)
open GlobalTheory.IndefiniteRowSideFullHecke.BoundaryPolynomialFunctions (IsProjective IsIrreducibleAnalytic IsIrreducibleComponent regularLocus regIntegral normSec absLogNorm boundary rFun poincarePot IsBoundarySetting)
open Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Hor GlobalTheory.Mean4O
open scoped ContDiff ComplexOrder ENNReal Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ArchLim

theorem isMDens_potDens_poincarePot : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (σ : κ.c.F →+* ℂ) [CompactSpace (CxPts (genStr s.T.Z) σ)] (m : ℕ) (α : LocPot (CxPts (genStr s.T.Z) σ)) (Λ : Fin m → LocPot (CxPts (genStr s.T.Z) σ)) (sg : Fin m → CxPts (genStr s.T.Z) σ → CxPts (genStr s.T.Z) σ → ℂ) (t : ℝ), IsBoundarySetting (manifold s.T.Z σ).finAtlas α Λ sg t → ∀ (Y : Scheme.{0}) (q : Y ⟶ Sp _) (jm : Y ⟶ s.T.Z.X) (hq : jm ≫ s.T.Z.s = q) (n : ℕ), IsMDens (D := n) (potDens (poincarePot α Λ sg t) (boundary sg)ᶜ (up jm hq σ)) := by
  intro D A N j S κ s σ _ m α Λ sg t hB Y q jm hq n
  have hol := fun ch => GlobalTheory.T.toroidal_chart_boundary_regular s.T.Z σ Y q jm hq n ch
  have sm := fun ch => GlobalTheory.T.boundary_setting_height_lower D A N j S κ s σ m α Λ sg t hB Y q jm hq n ch (hol ch)
  have he := fun ch => GlobalTheory.T.boundary_setting_height_upper D A N j S κ s σ m α Λ sg t hB Y q jm hq n ch (hol ch) (sm ch)
  refine ⟨fun ch ch' y hy hy' => ?_, fun ch => GlobalTheory.T.boundary_setting_height_comparison D A N j S κ s σ m α Λ sg t hB Y q jm hq n ch (sm ch) (he ch)⟩
  unfold potDens
  split_ifs with h
  · obtain ⟨O, hO, hyO, -, hsm⟩ := sm ch' (up jm hq σ y) y hy' h (α.mem_U _)
    have hd : ContDiffAt ℝ 2 (fun v => (poincarePot α Λ sg t).φ (up jm hq σ y) (up jm hq σ (ch'.e.symm v)))
        (ch'.e y) := (hsm.contDiffAt (hO.mem_nhds hyO)).of_le (by norm_cast)
    have ho := ChartGlue.isOpen_over ch.e ch'.e.open_source
    have hm := ChartGlue.mem_over ch.e hy hy'
    have e : (fun v => ((poincarePot α Λ sg t).φ (up jm hq σ y) (up jm hq σ (ch.e.symm v)) : ℂ)) =ᶠ[𝓝 (ch.e y)]
        (fun v => ((poincarePot α Λ sg t).φ (up jm hq σ y) (up jm hq σ (ch'.e.symm v)) : ℂ)) ∘ ch'.e ∘ ch.e.symm :=
      eventually_of_mem (ho.mem_nhds hm) fun v hv => by
        simp only [Function.comp_apply, ch'.e.left_inv hv.2]
    have e₂ : (ch'.e ∘ ch.e.symm) (ch.e y) = ch'.e y := congrArg ch'.e (ch.e.left_inv hy)
    rw [potMat, potMat, ReciprocityTheory.L2DbarEstimates.Y.cmpb_cHess_congr e,
      ReciprocityTheory.L2DbarEstimates.Y.cmpa_det_comp ho hm (ch.holo_trans ch') (e₂ ▸
        Complex.ofRealCLM.contDiff.contDiffAt.comp _ hd), e₂, Complex.re_ofReal_mul, ChartGlue.transDet]
    ring
  · simp

end GlobalTheory.ArchLim

end
