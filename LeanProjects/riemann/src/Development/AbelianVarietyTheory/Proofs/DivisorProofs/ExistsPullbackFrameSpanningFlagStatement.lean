import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPullbackFrameSpanningFlag
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalEqCurve
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjacentPullPull
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniREqUni
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFlagBundleIff
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.ArInt GlobalTheory.MixDens GlobalTheory.CovTest
open GlobalTheory.FlagFibre (Low uni dens)
open ReciprocityTheory.L2DbarEstimates (V cHess)
open scoped ContDiff ComplexOrder Classical
open GlobalTheory.FlagCell GlobalTheory.FlagConnect

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_pullback_frame_spanning_flag : ∀ (B Y : Scheme.{0}) (π : Y ⟶ B) (ι : Type) (r : ι → ℕ) (E : ι → B.Modules) (fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj (E a)) (r a)), (∀ a, IsVB (E a) (r a)) → ∀ (U : B.Opens) (eU : ∀ a, Fin (r a) → Γ(E a, U)), (∀ a, IsFrame (eU a)) → ∃ (W : Y.Opens) (hW : W ≤ π ⁻¹ᵁ U) (n : (Σ a, Low (r a)) → Γ(Y, W)), (∀ a, Spans (fl a) W (pullCol π (eU a) hW (uniR fun s => n ⟨a, s⟩))) ∧ ∀ (V : Y.Opens) (hV : V ≤ π ⁻¹ᵁ U) (n' : (Σ a, Low (r a)) → Γ(Y, V)), (∀ a, Spans (fl a) V (pullCol π (eU a) hV (uniR fun s => n' ⟨a, s⟩))) → ∃ hVW : V ≤ W, ∀ s, Y.presheaf.map (homOfLE hVW).op (n s) = n' s := by
  first | exact @GlobalTheory.FlagCell.exists_cellLocus | exact GlobalTheory.FlagCell.exists_cellLocus | (intros; apply GlobalTheory.FlagCell.exists_cellLocus <;> assumption)
