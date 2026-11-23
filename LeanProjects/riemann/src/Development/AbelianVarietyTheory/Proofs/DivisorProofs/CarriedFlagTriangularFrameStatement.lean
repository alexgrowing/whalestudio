import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CarriedFlagTriangularFrame
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
theorem _root_.GlobalTheory.T.carried_flag_triangular_frame : ∀ (B Y T : Scheme.{0}) (π : Y ⟶ B) (ι : Type) (r : ι → ℕ) (E : ι → B.Modules) (fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj (E a)) (r a)) (g' : T ⟶ Y) (g : T ⟶ B) (w : g' ≫ π = g) (fl' : ∀ a, Vert.Flag ((Scheme.Modules.pullback g).obj (E a)) (r a)), Carries π E r fl g' g w fl' → ∀ (U : B.Opens) (a : ι) (e : Fin (r a) → Γ(E a, U)) (V : Y.Opens) (hV : V ≤ π ⁻¹ᵁ U) (M : Matrix (Fin (r a)) (Fin (r a)) Γ(Y, V)) (V' : T.Opens) (h : V' ≤ g' ⁻¹ᵁ V) (h' : V' ≤ g ⁻¹ᵁ U), Spans (fl a) V (pullCol π e hV M) → Spans (fl' a) V' (pullCol g e h' (M.map (g'.appLE V V' h).hom)) := by
  first | exact @GlobalTheory.FlagCell.spans_pullCol_of_carries | exact GlobalTheory.FlagCell.spans_pullCol_of_carries | (intros; apply GlobalTheory.FlagCell.spans_pullCol_of_carries <;> assumption)
