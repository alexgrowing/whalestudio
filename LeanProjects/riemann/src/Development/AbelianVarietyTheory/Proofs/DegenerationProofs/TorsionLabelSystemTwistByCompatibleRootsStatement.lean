import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorsionLabelSystemTwistByCompatibleRoots
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsStrict
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex
open GlobalTheory.ModelData
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsionLabelSystem_twist_by_compatible_roots : ∀ (C : Type) [Field C] (N : NumD C) (La : Type) [AddCommGroup La] (EF : LinearMap.BilinForm ℤ La) (ζ : ℕ → Cˣ) (lab : ∀ k : ℕ, La → N.QT k) (k₀ : ℕ) (β : N.Form k₀) (u : Cˣ) (r : ℕ → Cˣ), Roots u r → Labels N EF ζ lab → ∀ p : ∀ k : ℕ, La → (N.twist β u).QT k, (∀ k, 0 < k → ∀ x, TwRel β u (r k) (lab k x) (p k x)) → Labels (N.twist β u) EF ζ p := by
  first | exact @GlobalTheory.TwistLabels.labels_twist | exact GlobalTheory.TwistLabels.labels_twist | (intros; apply GlobalTheory.TwistLabels.labels_twist <;> assumption)
