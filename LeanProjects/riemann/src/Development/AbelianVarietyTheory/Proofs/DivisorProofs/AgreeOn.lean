import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HilbertKodairaSpencer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitObj
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.RealMult

variable {F : Type} [Field F] [NumberField F] {𝔠 : FracId F}

def Rule.AgreeOn {R₀ : Type} [CommRing R₀] {k : ℕ} (s t : Rule (unitObj 𝔠 6) R₀ k) {A : Type} [CommRing A]
    (Y : Obj F 𝔠 (Sp A)) : Prop :=
  ∀ (B : Type) [CommRing B] [Algebra R₀ B] (σ : A →+* B) (Y' : Obj F 𝔠 (Sp B)) (φ : Y'.A.left ⟶ Y.A.left),
    Y'.IsPullBy Y (spMap σ) φ → ∀ (h : IsUnit ((6 : ℕ) : B)) (δ : Y'.DetGen), s.val B Y' h δ = t.val B Y' h δ

end GlobalTheory.RealMult
