import Mathlib
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.FormalGroupTranslateAutomorphismAndMatrixKernel
import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formalGroupTranslate_automorphism_and_matrixKernel : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] [CharZero V] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB V d O) (n : ℕ) (p : Matrix (Fin n) (Fin n) O), (0 ∈ kerM B p) ∧ (∀ f : PS V n d, shift B.G.F 0 f = f) ∧ ∀ α β : Fin n → Fin d → V, (∀ b, Small (α b)) → (∀ b, Small (β b)) → (∃ ψ : PS V n d ≃ₐ[V] PS V n d, ∀ f, shift B.G.F α f = ψ f) ∧ (α ∈ kerM B p ↔ ∀ f, shift B.G.F α (pullM B p f) = pullM B p f) ∧ ((∀ f, shift B.G.F α f = shift B.G.F β f) → α = β) ∧ ∃ δ : Fin n → Fin d → V, (∀ b, Small (δ b)) ∧ (∀ b, (cpt (δ b) : Pt V 0 d) = addV B.G.F (cpt (α b)) (cpt (β b))) ∧ (∀ f, shift B.G.F α (shift B.G.F β f) = shift B.G.F δ f) ∧ (α ∈ kerM B p → β ∈ kerM B p → δ ∈ kerM B p) := by
  first | exact @GlobalTheory.PlaceInt.shift_kerM | exact GlobalTheory.PlaceInt.shift_kerM | (intros; apply GlobalTheory.PlaceInt.shift_kerM <;> assumption)
