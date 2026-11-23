import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniTrait
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.Mum

def LabTors {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (A : PolAV (Sp (FractionRing R))) (k : ℕ)
    (x : QkPt D (Kb R) k → (TFK (R := R) (Kb R) ⟶ A.A)) : Prop :=
  (∀ y : TFK (R := R) (Kb R) ⟶ A.A, y ^ k = 1 → ∃ p, x p = y) ∧ (∀ p, x p ^ k = 1) ∧
    (∀ p p', x p = x p' ↔ QkPt.Equiv D (Kb R) p p') ∧
    (∀ p p' p'', QkAdd p p' p'' → x p'' = x p * x p') ∧
    ∀ p p' (z : (Kb R)ˣ), WeilQkIs D (Kb R) k p p' z ↔ WeilIs A.A A.L k (x p) (x p') (unitOn z)

end GlobalTheory.Mum
