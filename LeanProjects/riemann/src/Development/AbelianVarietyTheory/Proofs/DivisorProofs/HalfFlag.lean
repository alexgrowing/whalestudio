import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsAtOfNorms

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.ShFam.Pad

namespace GlobalTheory.WholeFlag

variable {F : Type} [Field F] [NumberField F] {Y : Var F}

def HalfFlag {C : CxSt F} {g : ℕ} (A : Fin g → Adl C Y) (p : ℕ) : Prop :=
  ∃ (V : Cover Y) (W : Y.X.Opens) (ι : Type) (U : ι → V.X.Opens)
    (M : ι → Matrix (Fin (g + g)) (Fin (g + g)) V.X.functionField) (J : Matrix (Fin (g + g)) (Fin (g + g)) ℤ)
    (c : ι → Fin g → V.G.functionFieldˣ), IsUnit J.det ∧ genericPoint Y.X ∈ W ∧
    (∀ x : V.X, ¬ IsUnit (p : V.X.presheaf.stalk x) → ∃ a, x ∈ U a) ∧
    (∀ a, ∀ x ∈ U a, ¬ IsUnit (p : V.X.presheaf.stalk x) → (∀ i k, RegAt x (M a i k)) ∧ UnitAt x (M a).det) ∧
    (∀ a i (z : V.G), V.j z ∈ U a → UnitAt z (V.φ (genAt (A i).D (V.π z)) * c a i)) ∧
    ∀ (v : HeightOneSpectrum (𝓞 F)), resP v = p → ∀ (e : Ext v) (y : AlgPt Y), below y.1 ∈ W →
      ∀ (z : Sp (AlgebraicClosure F) ⟶ V.G) (yt : Sp e.O ⟶ V.X), z ≫ V.π = y.1 → spMap e.O.subtype ≫ yt = z ≫ V.j →
      ∀ a, ⊤ ≤ yt ⁻¹ᵁ U a →
        (∀ i, (A i).lg v e y =
          Real.log (e.w (valAt z (V.φ (genAt (A i).D (below y.1)) * (c a i : V.G.functionField))))) ∧
        (∀ (i : Fin g) (k : Fin (g + g)), e.w (valAt (z ≫ V.j)
            (((M a).transpose * J.map (Int.castRingHom V.X.functionField) * M a) (Fin.castAdd g i) k) -
            (if (i : ℕ) + k = 2 * g - 1 then 1 else 0)) < 1) ∧
        ∀ b, ⊤ ≤ yt ⁻¹ᵁ U b → ∀ (k : Fin g) (i : Fin (g + g)),
          ((k : ℕ) < i → e.w (valAt (z ≫ V.j) (((M a)⁻¹ * M b) i (Fin.castAdd g k))) < 1) ∧
          e.w (valAt (z ≫ V.j) (((M a)⁻¹ * M b) (Fin.castAdd g k) (Fin.castAdd g k)) -
            valAt z ((c a k / c b k : V.G.functionFieldˣ) : V.G.functionField)) < 1

end GlobalTheory.WholeFlag

end
