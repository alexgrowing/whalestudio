import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsPrincipalMapDifferent

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

namespace GlobalTheory.LocM.LatCover

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
  {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}

def StepAt (Z B : Mdl Y i₀) (g : Z.X ⟶ B.X) (L : Lat B) (σ : E →+* ℂ) (r : ℕ) {U : Z.X.Opens} (hU : IsAffineOpen U)
    {V : B.X.Opens} {n : ℕ} (m : Fin n → Γ(L.N.toMod, V)) (a : GL (Fin n) Γ(Z.X, U)) : Prop :=
  ∀ (k : Type) [Field k] (φ : Γ(Z.X, U) →+* k) (v : Sp (DualNumber k) ⟶ B.t.G.left)
    (hv : IsTanAtG B.t ((spMap φ ≫ hU.fromSpec) ≫ g) v) (h : ⊤ ≤ ((spMap φ ≫ hU.fromSpec) ≫ g) ⁻¹ᵁ V),
    InStep Z B σ r (spMap φ ≫ hU.fromSpec) v →
    ∀ j : Fin n, r ≤ (j : ℕ) → ∑ l, φ (a j l) * tanEv B.t hv h (L.N.incl.app V (m l)) = 0

end GlobalTheory.LocM.LatCover
