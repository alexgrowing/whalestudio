import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsTorusActionWeightedCharts
import Development.AbelianVarietyTheory.Definitions.Degenerations.BaseFacts
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsAffineSplitTorusLeft
import Development.AbelianVarietyTheory.Definitions.Degenerations.CompanionTheory
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_torus_action_weighted_charts : Out.Laws → Out.Laws2 → ∀ (k : Type) [Field k] [IsAlgClosed k] (Φ : FibPre k) (g N N' : ℕ) (q : QuadraticMap ℤ Φ.E.X ℝ) (J : Type) [Fintype J] (cls : J → Φ.E.X) (F F' : J → (Φ.H 1).Sec) (π : Φ.Pol N) (m : Matrix J J k) (Ch : GlobalTheory.ZJ.Charts Φ.G.left) (e : Ch.I ≃ J) (cl : Φ.E.X → Ch.Cl), Big g N N' → Φ.Good N q cls F → π.PB.g + Module.finrank ℤ Φ.E.X = g → IsUnit m.det → (∀ i, IsLin Φ.G.hom F (m i) (F' i)) → (∀ α β, cl α = cl β ↔ ∃ n, α = β + N • n) → cl 0 = Ch.c₀ → (∀ i j, m (e i) j ≠ 0 → Ch.wt i = cl (cls j)) → (∀ i, Ch.W i = nonzeroLocus (F' (e i.1)) ∧ ∀ j, IsRatio (F' (e j)) (F' (e i.1)) (Ch.W i) (Ch.r i j)) → ∃ c : Fin (Module.finrank ℤ Φ.E.X) → Ch.Cl, GlobalTheory.ZJ.Charts.Split (H := Φ.G) Ch c := by
  first | exact @GlobalTheory.ZH.FibTorus.exists_split | exact GlobalTheory.ZH.FibTorus.exists_split | (intros; apply GlobalTheory.ZH.FibTorus.exists_split <;> assumption)
