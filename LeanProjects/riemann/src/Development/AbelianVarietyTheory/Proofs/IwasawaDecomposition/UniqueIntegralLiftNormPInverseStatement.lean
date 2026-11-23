import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UniqueIntegralLiftNormPInverse
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFlagFrame
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.LineNorm MonObj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unique_integral_lift_norm_p_inverse : HTBoundSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) [IsLocallyNoetherian X] (t : SAB H X) (p : ℕ) [Fact p.Prime] (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C] [CharZero C] [CompleteSpace C], ‖(p : C)‖ = (p : ℝ)⁻¹ → ∀ (x : Sp ↥(intO C) ⟶ X), (∀ x' : Sp ↥(intO C) ⟶ X, spMap (intO C).subtype ≫ x' = spMap (intO C).subtype ≫ x → x' = x) → ∀ (g : ℕ) (e : Fin g → (Sp (DualNumber ↥(intO C)) ⟶ t.G.left)), IsTanBasis t x e → ∀ (n : ℕ) (h : Fin n → Fin g → ↥(intO C)), (∀ c : TorsChar t x (p ^ 1), ∃ j, DlogIs t p 1 c e (h j)) → (∀ j, ∃ c : TorsChar t x (p ^ 1), DlogIs t p 1 c e (h j)) → ∀ (a : Fin g → C) (w : Sp (DualNumber C) ⟶ t.G.left), IsCombAtG t (spMap (intO C).subtype ≫ x) (fun i => spMap (dualMap (intO C).subtype) ≫ e i) a w → (w ∈ latHT t p (spMap (intO C).subtype ≫ x) ↔ (∀ j, ‖∑ i, (h j i : C) * a i‖ ≤ 1) ∧ ∀ i, ‖(p : C) * a i‖ ≤ 1) := by
  first | exact @GlobalTheory.HTLevel.mem_latHT_iff | exact GlobalTheory.HTLevel.mem_latHT_iff | (intros; apply GlobalTheory.HTLevel.mem_latHT_iff <;> assumption)
