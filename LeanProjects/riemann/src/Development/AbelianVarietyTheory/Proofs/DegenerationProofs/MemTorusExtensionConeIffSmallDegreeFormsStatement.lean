import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.MemTorusExtensionConeIffSmallDegreeForms
import Development.AbelianVarietyTheory.Definitions.Degenerations.PullChartIsLB
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_torusExtensionCone_iff_smallDegreeForms : Out.Laws → Out.Laws2 → (∀ (k : Type) [Field k] [IsAlgClosed k] (Φ : FibPre k) (g N N' : ℕ) (q : QuadraticMap ℤ Φ.E.X ℝ) (J : Type) [Fintype J] (cls : J → Φ.E.X) (F : J → (Φ.H 1).Sec) (π : Φ.Pol N), Big g N N' → Φ.Good N q cls F → π.PB.g + Module.finrank ℤ Φ.E.X = g → (N' : k) ≠ 0 → SmoothOfRelativeDimension g Φ.G.hom → (∀ d, 1 ≤ d → hilb (cone Φ.G.hom (Φ.H 1) F) d ≤ (N * d) ^ g) → ∀ v : J → k, v ∈ cone Φ.G.hom (Φ.H 1) F ↔ ((∃ i, cls i = 0 ∧ v i ≠ 0) ∧ ∀ (d : ℕ) (Pf : MvPolynomial J k), d ≤ N ^ g * g.factorial → Pf.IsHomogeneous d → (∀ x : Φ.Pt, x ^ N' = 1 → ∃ w, Crd (Φ.H 1) F x.left w ∧ MvPolynomial.eval w Pf = 0) → MvPolynomial.eval v Pf = 0)) := by
  first | exact @GlobalTheory.ZH.FibCone.mem_cone_iff | exact GlobalTheory.ZH.FibCone.mem_cone_iff | (intros; apply GlobalTheory.ZH.FibCone.mem_cone_iff <;> assumption)
