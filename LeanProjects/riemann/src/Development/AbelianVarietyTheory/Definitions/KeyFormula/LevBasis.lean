import Mathlib
import Development.AbelianVarietyTheory.Definitions.KeyFormula.IsSquareDeterminantComparison
import Development.AbelianVarietyTheory.Definitions.KeyFormula.KaRuleK
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.IsPluriharmonicSiegel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.MapsAtLeA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.OneEqSpTranslZero
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyPow GlobalTheory.KeyKa
noncomputable section
namespace GlobalTheory.KeyKa
open Matrix

def IsLevel {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ) (a b : Fin g → ℂ) (l : ℕ) (F : (Fin g → ℂ) → ℂ) : Prop :=
  Differentiable ℂ F ∧ ∀ (m n : Fin g → ℤ) (z : Fin g → ℂ),
    F (z + ((fun i => (m i : ℂ)) + τ.mulVec (fun i => (n i : ℂ)))) =
      Complex.exp (2 * Real.pi * Complex.I * (a ⬝ᵥ (fun i => (m i : ℂ)) - b ⬝ᵥ (fun i => (n i : ℂ)) -
        ((fun i => (n i : ℂ)) ⬝ᵥ τ.mulVec (fun i => (n i : ℂ))) / 2 - (fun i => (n i : ℂ)) ⬝ᵥ z)) ^ l * F z

def Wit (x : KeyIn ℂ) {g : ℕ} (h : x.P.g = g) (u : HolUnif x.P.A x.P.L g) (τ : Matrix (Fin g) (Fin g) ℂ) (a b : Fin g → ℂ) : Prop :=
  τ.IsSymm ∧ (τ.map Complex.im).PosDef ∧
    (∀ z, z ∈ u.Λ ↔ ∃ m n : Fin g → ℤ, z = (fun i => (m i : ℂ)) + τ.mulVec (fun i => (n i : ℂ))) ∧
    u.IsRig x.rig ∧ u.IsFn x.th (thetaChar τ a b) ∧
    ∀ i : Fin g, u.IsDiff (Pi.single i (2 * Real.pi * Complex.I)⁻¹) (x.v (i.cast h.symm))

def FnPw (x : KeyIn ℂ) {g : ℕ} (u : HolUnif x.P.A x.P.L g) {l : ℕ} (s : RR x l) (F : (Fin g → ℂ) → ℂ) : Prop :=
  ∀ i z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ x.P.L.U i → valAt' (u.ex z).left (x.P.L.U i) (s.f i) = F z * u.fr i z ^ l

def HolFam {g : ℕ} (W : Set (Fin g → Fin g → ℂ)) (F : (Fin g → Fin g → ℂ) → (Fin g → ℂ) → ℂ) : Prop :=
  DifferentiableOn ℂ (fun q : (Fin g → Fin g → ℂ) × (Fin g → ℂ) => F q.1 q.2) (W ×ˢ Set.univ)

abbrev per {g : ℕ} (p : Fin g → Fin g → ℂ) : Matrix (Fin g) (Fin g) ℂ := Key.phSym (Matrix.of p)

def LevBasis {g N : ℕ} (a b : Fin g → ℂ) (l : ℕ) (Th : Fin N → (Fin g → Fin g → ℂ) → (Fin g → ℂ) → ℂ) : Prop :=
  (∀ k, HolFam (Key.phDom g) (Th k)) ∧ ∀ p ∈ Key.phDom g, (∀ k, IsLevel (per p) a b l (Th k p)) ∧
    ∀ F, IsLevel (per p) a b l F → ∃! c : Fin N → ℂ, ∀ z, F z = ∑ k, c k * Th k p z

end GlobalTheory.KeyKa
end
