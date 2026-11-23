import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinePairExtensionCosSqBound
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalEqOfNonneg
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.CurveDens GlobalTheory.Cartier
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.line_pair_extension_cosSq_bound : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ) [CompactSpace (CxPts p σ)] [T2Space (CxPts p σ)] [SecondCountableTopology (CxPts p σ)], Nonempty (AnRead p σ 1) → ∀ (V L Q L' Q' : X.Modules) (l : L ⟶ V) (m : V ⟶ Q) (w : l ≫ m = 0) (l' : L' ⟶ V) (m' : V ⟶ Q') (w' : l' ≫ m' = 0) (hS : (ShortComplex.mk l m w).ShortExact) (hS' : (ShortComplex.mk l' m' w').ShortExact) (hL : IsVB L 1) (hQ : IsVB Q 1) (hL' : IsVB L' 1) (hQ' : IsVB Q' 1) (hl : IsSubbundle l) (hl' : IsSubbundle l') (h : Met p σ V (1 + 1)), h.IsCInf → ∀ v : CxPts p σ → ℝ, IsCosSq h l l' v → ∀ n : ℕ, total (fun (c : AlgChart p σ 1) y => v y ^ (n + 1) * (c.chernDens (h.restrict hl hL).detWeight y - c.chernDens (h.restrict hl' hL').detWeight y) + (n + 1) * v y ^ n * (1 - v y) * (Met.bcDens (S := ShortComplex.mk l m w) h hS hL hQ c y - Met.bcDens (S := ShortComplex.mk l' m' w') h hS' hL' hQ' c y)) = 0 := by
  first | exact @GlobalTheory.CurveDens.green_cosSq | exact GlobalTheory.CurveDens.green_cosSq | (intros; apply GlobalTheory.CurveDens.green_cosSq <;> assumption)
