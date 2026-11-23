import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlternatingPairingOnLattice
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (defCoord polydisc)
open scoped nonZeroDivisors
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.alternating_pairing_on_lattice : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (c : Ideal (OF E)) (y : (Af E)ˣ), c ≠ ⊥ →
    ∀ (𝔞 𝔟 : FracId (FR E)) (P : E → E → FR E),
    (∀ x ∈ lattice c y, ∀ x' ∈ lattice c y, P x x' = -P x' x) →
    (∀ x₁ ∈ lattice c y, ∀ x₂ ∈ lattice c y, ∀ x' ∈ lattice c y, P (x₁ + x₂) x' = P x₁ x' + P x₂ x') →
    (∀ (a : 𝓞 (FR E)), ∀ x ∈ lattice c y, ∀ x' ∈ lattice c y, P (((a : FR E) : E) * x) x' = (a : FR E) * P x x') →
    (∀ x ∈ lattice c y, ∀ x' ∈ lattice c y, P x x' ∈ dualLat (𝔞 * 𝔟⁻¹)) →
    (∀ t ∈ dualLat (𝔞 * 𝔟⁻¹), t ∈ Submodule.span (𝓞 (FR E)) {t | ∃ x ∈ lattice c y, ∃ x' ∈ lattice c y, t = P x x'}) →
    ∃ ω₁ ω₂ : E, (∀ x, x ∈ lattice c y ↔ ∃ m ∈ dualLat 𝔞, ∃ β ∈ 𝔟.elt, x = (m : E) * ω₁ + (β : E) * ω₂) ∧
      ∀ m ∈ dualLat 𝔞, ∀ β ∈ 𝔟.elt, ∀ m' ∈ dualLat 𝔞, ∀ β' ∈ 𝔟.elt,
        P ((m : E) * ω₁ + (β : E) * ω₂) ((m' : E) * ω₁ + (β' : E) * ω₂) = β * m' - m * β' := by
  first | exact @GlobalTheory.AltLattice.main | exact GlobalTheory.AltLattice.main | (intros; apply GlobalTheory.AltLattice.main <;> assumption)
