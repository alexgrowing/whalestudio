import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.DegenerationIsoCommInducedLabelMaps
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsStrict
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex
open GlobalTheory.ModelData
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.degenerationIso_comm_induced_label_maps : ∀ (C : Type) [NormedField C] (N N' : NumD C) (La : Type) [AddCommGroup La] (EF : LinearMap.BilinForm ℤ La) (ζ ζ' : ℕ → Cˣ) (lab : ∀ k : ℕ, La → N.QT k) (lab' : ∀ k : ℕ, La → N'.QT k) (n : ℕ), 1 < n → Labels N EF ζ lab → Labels N' EF ζ' lab' → ∀ J : NumD.Iso N N', (∀ j (p : N.QT (n ^ j)) (p' : N'.QT (n ^ j)), p'.1.1.toAdd = J.e p.1.1.toAdd → J.Rel p.1.2 p'.1.2 → ∃ x, N.QEq (lab _ x) p ∧ N'.QEq (lab' _ x) p') → (∀ j (y : N.X), ∃ p : N.QT (n ^ j), p.1.1.toAdd = y) → ∀ (α : N.X →+ N.X) (α' : N'.X →+ N'.X) (gam : La → La), (∀ j x, ∃ z, (lab (n ^ j) (gam x)).1.1.toAdd = α (lab (n ^ j) x).1.1.toAdd + n ^ j • z) → (∀ j x, ∃ z, (lab' (n ^ j) (gam x)).1.1.toAdd = α' (lab' (n ^ j) x).1.1.toAdd + n ^ j • z) → ∀ y, J.e (α y) = α' (J.e y) := by
  first | exact @GlobalTheory.ModelData.iso_comm_of_labels | exact GlobalTheory.ModelData.iso_comm_of_labels | (intros; apply GlobalTheory.ModelData.iso_comm_of_labels <;> assumption)
