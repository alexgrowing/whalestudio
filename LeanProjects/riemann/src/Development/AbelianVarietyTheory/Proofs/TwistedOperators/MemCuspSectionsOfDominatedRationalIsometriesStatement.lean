import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemCuspSectionsOfDominatedRationalIsometries
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIsCan
open NumberField AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.HeckeEx
open GlobalTheory.Dict (castFr)
open GlobalTheory.FrameNorm (IsUnitFr)
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_cuspSections_of_dominated_rational_isometries : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (I₀ : Type) [Finite I₀] (X' : I₀ → Data E r) (la : Wt X.Ψ r) (la' : ∀ j, Wt (X' j).Ψ r) (P : Frame X.Ψ r → ℂ) (Q : ∀ j, Frame (X' j).Ψ r → ℂ) (N : ℕ) (M : ℝ), 0 < N → 0 ≤ M → X.IsSec la P → (∀ j, Q j ∈ (X' j).SS (la' j)) → (∀ j a (h : QMatch X (X' j) N a) τ m, la' j τ m = la ⟨τ.1, h.mem τ⟩ m) → (∀ x ∈ X.dom, ∀ B : ℝ, 0 ≤ B → (∀ j a (h : QMatch X (X' j) N a), ‖Q j (lact a (castFr h.psi x))‖ ≤ B) → ‖P x‖ ≤ M * B) → P ∈ X.SS la := by
  first | exact @GlobalTheory.HeckeEx.mem_SS_of_dom | exact GlobalTheory.HeckeEx.mem_SS_of_dom | (intros; apply GlobalTheory.HeckeEx.mem_SS_of_dom <;> assumption)
