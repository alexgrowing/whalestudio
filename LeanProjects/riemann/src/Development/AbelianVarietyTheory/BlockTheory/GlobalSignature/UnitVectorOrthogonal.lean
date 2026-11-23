import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.HermitianLattices.StatementLat

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.UnitVectorOrthogonal

open NumberField Formalism.BasicNotions

section Generic

variable {E : Type} [Field E] [NumberField E] [StarRing E]

def OfKind (W : HSpace E) (M P Q : ℕ) : Prop :=
  W.rank = M ∧ W.SigOK ∧ ∀ τ : E →+* ℂ, W.sig τ = (P, Q)

def perp (W : HSpace E) (x : W.V) : Submodule E W.V := LinearMap.ker (W.hT x)

def perpLat (W : HSpace E) (L : Submodule (𝓞 E) W.V) (x : W.V) : Submodule (𝓞 E) W.V :=
  L ⊓ (perp W x).restrictScalars (𝓞 E)

def IsSelfDualLat (W : HSpace E) (L : Submodule (𝓞 E) W.V) : Prop :=
  Submodule.IsLattice E L ∧ Formalism.HermitianLatticesTheory.dual W.hT L = L

def HasComplement (W : HSpace E) (x : W.V) (M' P' Q' : ℕ) : Prop :=
  ∃ L : Submodule (𝓞 E) W.V, IsSelfDualLat W L ∧ x ∈ L ∧
    L = Submodule.span (𝓞 E) {x} ⊔ perpLat W L x ∧
    ∃ (W' : HSpace E) (ι : W'.V →ₗ[E] W.V), OfKind W' M' P' Q' ∧
      HSpace.IsIsomEmb W' W ι ∧ LinearMap.range ι = perp W x ∧
      W'.L0.map (ι.restrictScalars (𝓞 E)) = perpLat W L x

def UnitVectorPerpOver (E : Type) [Field E] [NumberField E] [StarRing E] : Prop :=
  ∀ (W : HSpace E) (M P Q : ℕ), OfKind W M P Q → 3 ≤ M →
    (1 ≤ P → ∃ x : W.V, W.hD x x = 1 ∧ HasComplement W x (M - 1) (P - 1) Q) ∧
    (1 ≤ Q → ∃ x : W.V, W.hD x x = -1 ∧ HasComplement W x (M - 1) P (Q - 1))

def UnitVectorPerpEveryOver (E : Type) [Field E] [NumberField E] [StarRing E] : Prop :=
  ∀ (W : HSpace E) (M P Q : ℕ), OfKind W M P Q → 3 ≤ M →
    (1 ≤ P → (∃ x : W.V, W.hD x x = 1) ∧
      ∀ x : W.V, W.hD x x = 1 → HasComplement W x (M - 1) (P - 1) Q) ∧
    (1 ≤ Q → (∃ x : W.V, W.hD x x = -1) ∧
      ∀ x : W.V, W.hD x x = -1 → HasComplement W x (M - 1) P (Q - 1))

end Generic

def UnitVectorPerp (D : D7) : Prop :=
  letI := D.host.cmStar
  UnitVectorPerpOver D.host.E

def UnitVectorPerpEvery (D : D7) : Prop :=
  letI := D.host.cmStar
  UnitVectorPerpEveryOver D.host.E

end GlobalTheory.IndefiniteRowSideFullHecke.UnitVectorOrthogonal

end
