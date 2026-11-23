import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TwistIsoTorsionRepresentativeMulEquiv
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.WithISelf
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Relabel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twist_iso_torsionRepresentative_mulEquiv : ∀ (O : Type) [CommRing O] (N N' : NumD O) (k : ℕ) (β : N.Form k) (u : Oˣ) (J : NumD.Iso (N.twist β u) N'), (∀ (r : Oˣ) (j : ℕ), r ^ j = u → ∃ τ : N.QT j ≃* N'.QT j, (∀ q q', τ q = q' ↔ TwJ β u r J q q') ∧ (∀ q₁ q₂, N.QEq q₁ q₂ ↔ N'.QEq (τ q₁) (τ q₂)) ∧ ∀ q₁ q₂, N'.wp (τ q₁) (τ q₂) = N.wp q₁ q₂) ∧ ∀ (r₁ r₂ : Oˣ) (n n' m : ℕ) (q₁ : N.QT n) (q₂ : N.QT n') (q₁' : N'.QT n) (q₂' : N'.QT n'), r₂ ^ m = r₁ → q₁.1.1 = q₂.1.1 → q₁.1.2 = q₂.1.2 ^ m → TwJ β u r₁ J q₁ q₁' → TwJ β u r₂ J q₂ q₂' → q₁'.1.1 = q₂'.1.1 ∧ q₁'.1.2 = q₂'.1.2 ^ m := by
  first | exact @GlobalTheory.Relabel.twJ_mulEquiv | exact GlobalTheory.Relabel.twJ_mulEquiv | (intros; apply GlobalTheory.Relabel.twJ_mulEquiv <;> assumption)
