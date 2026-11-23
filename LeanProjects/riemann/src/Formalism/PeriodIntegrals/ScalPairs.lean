import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermDef

noncomputable section

open scoped Classical

namespace PI.ScalPairs

open NumberField Module Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermDef

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ}

def ScalRel (Λ : Submodule (𝓞 E) S.V) (g k : ℕ) {T T' : E} (F : LFlag S r T) (F' F'' : LFlag S r T') : Prop :=
  ∃ β : S.V ≃ₗ[E] S.V, IsPair Λ F F' F'' β g ∧ s0 Λ F F' F'' β k = 1 ∧ IsScalar Λ F F' F'' β

end Gen

def Unram (E : Type) [Field E] [NumberField E] (p : ℕ) : Prop :=
  ∀ (Q : Ideal (𝓞 E)) [Q.IsPrime] [Q.LiesOver (Ideal.span {(p : ℤ)})], Q.ramificationIdx ℤ = 1

def ScalarEquivG : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (S : HSpace E) (r k g : ℕ),
    finrank E S.V = k + 2 * r + 1 →
    ∀ Λ : Submodule (𝓞 E) S.V, Submodule.IsLattice E Λ →
    ∀ (T T' : E), T ≠ 0 → T' ≠ 0 → ∀ F : LFlag S r T, IsLift Λ F →
      Equivalence (fun x y : {F' : LFlag S r T' // IsLift Λ F' ∧ Gval F F' ≠ 0} => ScalRel Λ g k F x.1 y.1)

section D7

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable (D : D7)

def ScalRelD {u : D.what₂.Word} (u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E))
    (Λ : Submodule (𝓞 D.host.E) (VS D).V)
    (x y : {x : Carrier (PD D Λ (lf D F0) u') // Gval (lf D F0) x.1 ≠ 0}) : Prop :=
  ScalRel Λ (gS D) D.R.k (lf D F0) x.1.1 y.1.1

def ScalarEquiv (u u' : D.what₂.Word) : Prop :=
  ∀ (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (Λ : Submodule (𝓞 D.host.E) (VS D).V),
    IsRowLat D F0 Λ → Equivalence (ScalRelD D u' F0 Λ)

def BetaL (u u' : D.what₂.Word) : Prop :=
  (∀ i, 3 ≤ D.host.g i ∧ Unram D.host.E (D.host.g i)) →
  ∀ (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (Λ : Submodule (𝓞 D.host.E) (VS D).V),
    IsRowLat D F0 Λ → ∀ x y : Carrier (PD D Λ (lf D F0) u'),
      Gval (lf D F0) x.1 ≠ 0 → Gval (lf D F0) y.1 ≠ 0 →
      ∀ β₁ β₂ : (VS D).V ≃ₗ[D.host.E] (VS D).V,
        IsPair Λ (lf D F0) x.1 y.1 β₁ (gS D) → IsPair Λ (lf D F0) x.1 y.1 β₂ (gS D) →
        ∀ v ∈ orth (VS D) (Xsp x.1), β₁ v - β₂ v ∈ Xsp y.1

def BetaFree (u u' : D.what₂.Word) : Prop :=
  (∀ i, 3 ≤ D.host.g i ∧ Unram D.host.E (D.host.g i)) →
  ∀ (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (Λ : Submodule (𝓞 D.host.E) (VS D).V),
    IsRowLat D F0 Λ → ∀ x y : Carrier (PD D Λ (lf D F0) u'),
      Gval (lf D F0) x.1 ≠ 0 → Gval (lf D F0) y.1 ≠ 0 →
      ∀ β₁ β₂ : (VS D).V ≃ₗ[D.host.E] (VS D).V,
        IsPair Λ (lf D F0) x.1 y.1 β₁ (gS D) → IsPair Λ (lf D F0) x.1 y.1 β₂ (gS D) →
        Lat.s0 Λ (lf D F0) x.1 y.1 β₁ D.R.k = Lat.s0 Λ (lf D F0) x.1 y.1 β₂ D.R.k ∧
        (IsScalar Λ (lf D F0) x.1 y.1 β₁ ↔ IsScalar Λ (lf D F0) x.1 y.1 β₂)

end D7

end PI.ScalPairs
