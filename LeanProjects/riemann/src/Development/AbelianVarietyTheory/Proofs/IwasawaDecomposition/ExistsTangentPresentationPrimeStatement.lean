import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTangentPresentationPrime
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFlagFrame
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.LineNorm MonObj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_tangent_presentation_prime : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) [IsLocallyNoetherian X] (t : SAB H X) (A : Type) [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [CharZero A] (x₀ : Sp A ⟶ X) (g : ℕ) (e : Fin g → (Sp (DualNumber A) ⟶ t.G.left)), IsTanBasis t x₀ e → ∀ p : ℕ, p.Prime → (∃ ζ : A, IsPrimitiveRoot ζ p) → SplitTors t x₀ p → ∃ (n : ℕ) (h : Fin n → Fin g → A), ∀ (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C] [CharZero C] (x : A →+* ↥(intO C)), (∀ c : TorsChar t (spMap x ≫ x₀) (p ^ 1), ∃ j, DlogIs t p 1 c (fun i => spMap (dualMap x) ≫ e i) (fun i => x (h j i))) ∧ ∀ j, ∃ c : TorsChar t (spMap x ≫ x₀) (p ^ 1), DlogIs t p 1 c (fun i => spMap (dualMap x) ≫ e i) (fun i => x (h j i)) := by
  first | exact @GlobalTheory.HTMap.hodgeTate_map | exact GlobalTheory.HTMap.hodgeTate_map | (intros; apply GlobalTheory.HTMap.hodgeTate_map <;> assumption)
