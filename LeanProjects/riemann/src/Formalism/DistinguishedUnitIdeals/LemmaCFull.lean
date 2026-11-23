import Mathlib
import Formalism.DistinguishedUnitIdeals.ArcLiftOfLocalizationData
import Formalism.DistinguishedUnitIdeals.Statement

noncomputable section

namespace Formalism.ExponentWindows.E

open PowerSeries

def Base.PShape {O : Type} [CommRing O] (B : Base O) (ell : ℕ) : Prop :=
  ∀ s < ell, ∃ (E : Polynomial O) (u : PowerSeries O), E.Monic ∧ E.natDegree = B.ℓ ^ s ∧
    (∀ i < B.ℓ ^ s, (B.ℓ : O) ∣ E.coeff i) ∧ Associated (E.coeff 0) (B.ℓ : O) ∧ IsUnit u ∧
    B.p s = u * (E : PowerSeries O)

def LevelData.FlReg {O : Type} [CommRing O] {B : Base O} {n : ℕ} {V : Type} [AddCommGroup V]
    [Module (PowerSeries O) V] {L : Lat B n V} {c : ZMod n} {ell : ℕ} {Λ : PowerSeries O} {r : ℕ}
    (S : LevelData L c ell Λ r) (ϖ : O) (H : ℕ → ℕ) : Prop :=
  ∀ s < ell, ∀ y : Fin r → PowerSeries O, S.locL s y ∈ S.Fl s →
    ∃ (N : ℕ) (z : Fin r → PowerSeries O), C (ϖ ^ N) • y = B.p s ^ H s • z

def CMap {O : Type} [CommRing O] {r₁ r₂ : ℕ} (C₁ : Submodule O (Fin r₁ → O))
    (C₂ : Submodule O (Fin r₂ → O)) (prL : (Fin r₁ → O) →ₗ[O] (Fin r₂ → O)) : Prop :=
  ∀ v ∈ C₁, prL v ∈ C₂

def LemmaCFull : Prop :=
  LemmaCValR → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O),
    Irreducible ϖ → ∀ (B : Base O) (e : ℕ), 1 ≤ e → Associated (B.ℓ : O) (ϖ ^ e) →
    ∀ (n : ℕ) (V₁ V₂ : Type) [AddCommGroup V₁] [Module (PowerSeries O) V₁] [AddCommGroup V₂]
      [Module (PowerSeries O) V₂] (L₁ : Lat B n V₁) (L₂ : Lat B n V₂) (h : LatHom L₁ L₂)
      (c : ZMod n) (ell : ℕ) (Λ : PowerSeries O) (r₁ r₂ : ℕ)
      (S₁ : LevelData L₁ c ell Λ r₁) (S₂ : LevelData L₂ c ell Λ r₂) (m : LevelMap h S₁ S₂)
      (H b : ℕ → ℕ) (kind : ℕ → Kind)
      (U₁ : ℕ → Submodule O (Fin r₁ → O)) (U₂ : ℕ → Submodule O (Fin r₂ → O))
      (g sig rr a₀ : ℕ),
      Λ = Formalism.ExponentWindows.abelian₂ B.p H ell → B.PShape ell →
      LevelModelSetting ϖ B.ℓ ell B.p H b kind U₁ U₂ →
      S₁.RD g → S₂.RD g → S₁.Partner sig → S₂.Partner sig → S₁.P3 → S₂.P3 →
      S₁.DivisibleIff g → S₂.DivisibleIff g →
      S₁.Bridge ϖ H b kind U₁ → S₂.Bridge ϖ H b kind U₂ → S₂.FlReg ϖ H →
      m.MapFl → h.LiftsDivisible c ell g rr →
      ∀ s₀ s₁ : ℕ, s₀ < s₁ → s₁ < ell → kind s₁ = Kind.up → kind s₀ = Kind.down →
      (∀ s < ell, s ≠ s₀ → s ≠ s₁ → kind s = Kind.thin) →
      CMap (U₁ s₁) (U₂ s₁) m.prL →
      2 * sig + rr + 2 * g * ell ≤ a₀ → 2 * a₀ < b s₁ → 2 * b s₀ ≤ B.ℓ * b s₁ →
      CLift B.ℓ a₀ (U₁ s₁) (U₂ s₁) m.prL

end Formalism.ExponentWindows.E
