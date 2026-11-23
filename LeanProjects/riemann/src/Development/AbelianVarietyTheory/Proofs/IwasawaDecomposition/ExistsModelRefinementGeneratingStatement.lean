import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsModelRefinementGenerating
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFlagFrame
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.LineNorm MonObj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_model_refinement_generating : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (M : GlobalTheory.TrueGeo.Model Y) (Δ : Y.Dv) (t : Y.X → Y.Fnˣ) (V : M.X.Opens) (d n : ℕ) (s : Fin n → Y.Fn) (z : M.X), (∀ y, Δ.IsEqn y (t y)) → z ∈ V → Generates M t V d s → ∃ (N : GlobalTheory.TrueGeo.Model Y) (π : N.X ⟶ M.X) (V' : M.X.Opens), N.j ≫ π = M.j ∧ π ≫ M.p = N.p ∧ z ∈ V' ∧ V' ≤ V ∧ ∀ x ∈ π ⁻¹ᵁ V', ∃ (i : Fin n) (W : N.X.Opens), x ∈ W ∧ s i ≠ 0 ∧ ∀ k, ∃ g : Γ(N.X, W), ∀ h : genericPoint Y.X ∈ N.j ⁻¹ᵁ W, fnOf (N.j ⁻¹ᵁ W) h (N.j.app W g) * s i = s k := by
  first | exact @GlobalTheory.InvertIdeal.main | exact GlobalTheory.InvertIdeal.main | (intros; apply GlobalTheory.InvertIdeal.main <;> assumption)
