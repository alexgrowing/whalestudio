import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleCarriesBaseChange
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
theorem _root_.GlobalTheory.T.flag_bundle_carries_base_change : ∀ (B Y : Scheme.{0}) (π : Y ⟶ B) (ι : Type) [Fintype ι] (r : ι → ℕ) (E : ι → B.Modules) (fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj (E a)) (r a)), (∀ a, IsVB (E a) (r a)) → ∀ (U : B.Opens) (eU : ∀ a, Fin (r a) → Γ(E a, U)), (∀ a, IsFrame (eU a)) → ∀ (T : Scheme.{0}) (g' : T ⟶ Y) (g : T ⟶ B) (w : g' ≫ π = g) (fl' : ∀ a, Vert.Flag ((Scheme.Modules.pullback g).obj (E a)) (r a)), Carries π E r fl g' g w fl' → ∀ (V' : T.Opens) (hV' : V' ≤ g ⁻¹ᵁ U) (n' : (Σ a, Low (r a)) → Γ(T, V')), (∀ a, Spans (fl' a) V' (pullCol g (eU a) hV' (uniR fun s => n' ⟨a, s⟩))) → ∀ t ∈ V', ∃ (V : Y.Opens) (hV : V ≤ π ⁻¹ᵁ U) (n : (Σ a, Low (r a)) → Γ(Y, V)), g' t ∈ V ∧ ∀ a, Spans (fl a) V (pullCol π (eU a) hV (uniR fun s => n ⟨a, s⟩)) := by
  first | exact @GlobalTheory.FlagCell.CellOpen.spans_uniR_near_image | exact GlobalTheory.FlagCell.CellOpen.spans_uniR_near_image | (intros; apply GlobalTheory.FlagCell.CellOpen.spans_uniR_near_image <;> assumption)
