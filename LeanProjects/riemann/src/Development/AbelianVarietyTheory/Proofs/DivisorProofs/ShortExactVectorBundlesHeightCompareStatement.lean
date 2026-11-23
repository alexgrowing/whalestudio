import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShortExactVectorBundlesHeightCompare
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalEqCurve
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjacentPullPull
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.ArInt GlobalTheory.MixDens GlobalTheory.CovTest
open GlobalTheory.FlagFibre (Low uni dens)
open ReciprocityTheory.L2DbarEstimates (V cHess)
open scoped ContDiff ComplexOrder Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.short_exact_vector_bundles_height_compare : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ) (d : ℕ) [CompactSpace (CxPts p σ)] [T2Space (CxPts p σ)] [SecondCountableTopology (CxPts p σ)], Nonempty (AnRead p σ (d + 1)) → ∀ (E L Q L' Q' : X.Modules) (l : L ⟶ E) (m : E ⟶ Q) (w : l ≫ m = 0) (l' : L' ⟶ E) (m' : E ⟶ Q') (w' : l' ≫ m' = 0) (hS : (ShortComplex.mk l m w).ShortExact) (hS' : (ShortComplex.mk l' m' w').ShortExact) (hL : IsVB L 1) (hQ : IsVB Q 1) (hL' : IsVB L' 1) (hQ' : IsVB Q' 1) (hl : IsSubbundle l) (hl' : IsSubbundle l') (h : Met p σ E (1 + 1)), h.IsCInf → ∀ (N : LB X) (φ : Weight p σ N), φ.IsCInf → ∀ v : CxPts p σ → ℝ, CurveDens.IsCosSq h l l' v → ∀ n : ℕ, total (fun (c : AlgChart p σ (d + 1)) y => v y ^ (n + 1) * (mix d (chernMat φ c y) (chernMat (h.restrict hl hL).detWeight c y) - mix d (chernMat φ c y) (chernMat (h.restrict hl' hL').detWeight c y)) + (n + 1) * v y ^ n * (1 - v y) * (mix d (chernMat φ c y) (bcMat (S := ShortComplex.mk l m w) h hS hL hQ c y) - mix d (chernMat φ c y) (bcMat (S := ShortComplex.mk l' m' w') h hS' hL' hQ' c y))) = 0 := by
  first | exact @GlobalTheory.MixDens.green_cosSq | exact GlobalTheory.MixDens.green_cosSq | (intros; apply GlobalTheory.MixDens.green_cosSq <;> assumption)
