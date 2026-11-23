import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DRChainStdSt

open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped NumberField TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IwLevel

open GlobalTheory.UPel.HT

def HTIw.LineCert {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}
    {A : Type} [CommRing A] {σ : R →+* A} {o : Obj b N (spMap σ)} {w : Ideal (𝓞 D.F)} (c : HTIw o w)
    (i : Fin D.a) (ε : A ⊗[ℤ] D.O) {a : 𝓞 D.F} (ha : a ∈ w) (f : A) : Prop :=
  ∀ j, ∃ s ∈ (c.drChain i ε ha).ω j, ∃ l : (c.drChain i ε ha).M j →ₗ[A] A, l s = f ∧
    ∀ z ∈ (c.drChain i ε ha).ω j, ∃ (n : ℕ) (r : A), f ^ n • z = r • s

end GlobalTheory.IwLevel
