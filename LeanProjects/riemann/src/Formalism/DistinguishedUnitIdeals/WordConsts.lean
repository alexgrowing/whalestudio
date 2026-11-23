import Mathlib
import Formalism.DistinguishedUnitIdeals.ArcLiftOfLocalizationData

noncomputable section

namespace Formalism.ExponentWindows.E

open PowerSeries

def WordNone (ell : ℕ) (kind : ℕ → Kind) : Prop :=
  ∀ s < ell, kind s ≠ Kind.down

def WordD (ell : ℕ) (kind : ℕ → Kind) : Prop :=
  ∃ s₁ : ℕ, s₁ < ell ∧ kind s₁ = Kind.down ∧ ∀ s < ell, s ≠ s₁ → kind s = Kind.thin

def WordDU (ℓ ell : ℕ) (b : ℕ → ℕ) (kind : ℕ → Kind) : Prop :=
  ∃ s₀ s₁ : ℕ, s₀ < s₁ ∧ s₁ < ell ∧ kind s₁ = Kind.down ∧ kind s₀ = Kind.up ∧
    (∀ s < ell, s ≠ s₀ → s ≠ s₁ → kind s = Kind.thin) ∧ b s₀ < ℓ * b s₁

def WordDD {O : Type} [CommRing O] (ϖ : O) (ell : ℕ) (p : ℕ → PowerSeries O) (b : ℕ → ℕ)
    (kind : ℕ → Kind) : Prop :=
  ∃ s₀ s₁ : ℕ, s₀ < s₁ ∧ s₁ < ell ∧ kind s₁ = Kind.down ∧ kind s₀ = Kind.down ∧
    (∀ s < ell, s ≠ s₀ → s ≠ s₁ → kind s = Kind.thin) ∧
    ∃ (ρ : ℕ) (fρ : PowerSeries O),
      C (ϖ ^ ρ) ∈ Ideal.span {p s₁ ^ b s₁, p s₀ ^ b s₀} ∧
      (∀ k : ℕ, C (ϖ ^ k) ∈ Ideal.span {p s₁ ^ b s₁, p s₀ ^ b s₀} → ρ ≤ k) ∧
      fρ ∈ Ideal.span {p s₁ ^ b s₁} ∧ fρ - C (ϖ ^ ρ) ∈ Ideal.span {p s₀ ^ b s₀}

def WordUD {O : Type} [CommRing O] {r₁ r₂ : ℕ} (ϖ : O) (ℓ ell a₀ : ℕ) (p : ℕ → PowerSeries O)
    (b : ℕ → ℕ) (kind : ℕ → Kind) (U₁ : ℕ → Submodule O (Fin r₁ → O))
    (U₂ : ℕ → Submodule O (Fin r₂ → O)) (prL : (Fin r₁ → O) →ₗ[O] (Fin r₂ → O)) : Prop :=
  ∃ s₀ s₁ : ℕ, s₀ < s₁ ∧ s₁ < ell ∧ kind s₁ = Kind.up ∧ kind s₀ = Kind.down ∧
    (∀ s < ell, s ≠ s₀ → s ≠ s₁ → kind s = Kind.thin) ∧
    CLift ℓ a₀ (U₁ s₁) (U₂ s₁) prL ∧
    ∃ (c : ℕ) (α β : PowerSeries O),
      p s₁ ^ b s₁ = C (ϖ ^ c) * α + p s₀ ^ b s₀ * β ∧
      p s₁ ^ b s₁ ∉ Ideal.span {C (ϖ ^ (c + 1)), p s₀ ^ b s₀}

def ArcWord {O : Type} [CommRing O] {r₁ r₂ : ℕ} (ϖ : O) (ℓ ell a₀ : ℕ) (p : ℕ → PowerSeries O)
    (b : ℕ → ℕ) (kind : ℕ → Kind) (U₁ : ℕ → Submodule O (Fin r₁ → O))
    (U₂ : ℕ → Submodule O (Fin r₂ → O)) (prL : (Fin r₁ → O) →ₗ[O] (Fin r₂ → O)) : Prop :=
  WordNone ell kind ∨ WordD ell kind ∨ WordDU ℓ ell b kind ∨ WordDD ϖ ell p b kind ∨
    WordUD ϖ ℓ ell a₀ p b kind U₁ U₂ prL

def WordConsts : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (ℓ ell : ℕ) (p : ℕ → PowerSeries O) (b : ℕ → ℕ), 2 ≤ ℓ → DistinguishedFamily ϖ ℓ ell p →
      ∀ s₀ s₁ : ℕ, s₀ < s₁ → s₁ < ell →
      (∃ (ρ : ℕ) (fρ : PowerSeries O),
        C (ϖ ^ ρ) ∈ Ideal.span {p s₁ ^ b s₁, p s₀ ^ b s₀} ∧
        (∀ k : ℕ, C (ϖ ^ k) ∈ Ideal.span {p s₁ ^ b s₁, p s₀ ^ b s₀} → ρ ≤ k) ∧
        fρ ∈ Ideal.span {p s₁ ^ b s₁} ∧ fρ - C (ϖ ^ ρ) ∈ Ideal.span {p s₀ ^ b s₀}) ∧
      (1 ≤ b s₀ → ∃ (c : ℕ) (α β : PowerSeries O),
        p s₁ ^ b s₁ = C (ϖ ^ c) * α + p s₀ ^ b s₀ * β ∧
        p s₁ ^ b s₁ ∉ Ideal.span {C (ϖ ^ (c + 1)), p s₀ ^ b s₀})

section
variable {O : Type} [CommRing O] {B : Base O} {n : ℕ} {V₁ V₂ : Type} [AddCommGroup V₁]
  [Module (PowerSeries O) V₁] [AddCommGroup V₂] [Module (PowerSeries O) V₂]
  {L₁ : Lat B n V₁} {L₂ : Lat B n V₂}

def ArcProps (h : LatHom L₁ L₂) (c : ZMod n) (ell : ℕ) (Λ : PowerSeries O)
    (g sig rr a₀ kap : ℕ) (ϖ : O) {r₁ r₂ : ℕ}
    (S₁ : LevelData L₁ c ell Λ r₁) (S₂ : LevelData L₂ c ell Λ r₂) (m : LevelMap h S₁ S₂)
    (H b : ℕ → ℕ) (kind : ℕ → Kind) (U₁ : ℕ → Submodule O (Fin r₁ → O))
    (U₂ : ℕ → Submodule O (Fin r₂ → O)) (PP PP' : Polynomial O) : Prop :=
  Λ = Formalism.ExponentWindows.abelian₂ B.p H ell ∧
  L₁.GammaCongruentArc c ell Λ ∧ L₂.GammaCongruentArc c ell Λ ∧
  S₁.Equiv ∧ S₂.Equiv ∧ S₂.K2iii ∧ S₁.RD g ∧ S₂.RD g ∧ S₂.K3a2 g PP ∧ S₁.K3a4 g PP' ∧
  S₁.DcFix ∧ S₁.Partner sig ∧ S₂.Partner sig ∧ S₁.P3 ∧ S₂.P3 ∧
  S₁.DivisibleIff g ∧ S₂.DivisibleIff g ∧ S₁.XMulIff ∧ S₂.XMulIff ∧
  S₁.Bridge ϖ H b kind U₁ ∧ S₂.Bridge ϖ H b kind U₂ ∧
  m.MapFl ∧ h.LiftsDivisible c ell g rr ∧ PPval B.ℓ kap PP PP' ∧
  LevelModelSetting ϖ B.ℓ ell B.p H b kind U₁ U₂ ∧ LLift B.ℓ rr m.prL ∧
  ArcWord ϖ B.ℓ ell a₀ B.p b kind U₁ U₂ m.prL

def ArcHyp (h : LatHom L₁ L₂) (c : ZMod n) (ell : ℕ) (Λ : PowerSeries O)
    (g sig rr a₀ kap : ℕ) (ϖ : O) : Prop :=
  ∃ (r₁ r₂ : ℕ) (S₁ : LevelData L₁ c ell Λ r₁) (S₂ : LevelData L₂ c ell Λ r₂)
    (m : LevelMap h S₁ S₂) (H b : ℕ → ℕ) (kind : ℕ → Kind) (U₁ : ℕ → Submodule O (Fin r₁ → O))
    (U₂ : ℕ → Submodule O (Fin r₂ → O)) (PP PP' : Polynomial O),
    ArcProps h c ell Λ g sig rr a₀ kap ϖ S₁ S₂ m H b kind U₁ U₂ PP PP'

end

def ThmEFull : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (B : Base O) (n : ℕ) [NeZero n] (Cu : Cuts n)
    (abelian₂ : ZMod n → PowerSeries O) (j M g sig rr a₀ kap : ℕ)
    (V₁ V₂ V₀ : Type) [AddCommGroup V₁] [Module (PowerSeries O) V₁] [AddCommGroup V₂]
    [Module (PowerSeries O) V₂] [AddCommGroup V₀] [Module (PowerSeries O) V₀]
    (L₁ : Lat B n V₁) (L₂ : Lat B n V₂) (L₀ : Lat B n V₀) (e₀ : V₀) (h : LatHom L₁ L₂)
    (Zf₁ : AddSubgroup ((ZMod n → V₁) × (ZMod n → V₁)))
    (Zf₂ : AddSubgroup ((ZMod n → V₂) × (ZMod n → V₂))),
    1 ≤ M → B.Good j M g → L₁.Good Cu j M g sig → L₂.Good Cu j M g sig →
    (∀ c ∈ Cu.cuts, j ≤ Cu.ell c) → (∀ i, L₀.φ i e₀ = e₀) → (∀ i, L₀.γ i e₀ = e₀) →
    (∀ (m : O), ∀ κ ∈ Zf₁, (C m • κ.1, C m • κ.2) ∈ Zf₁) →
    (∀ c ∈ Cu.cuts, ∀ w, L₁.Wc Cu abelian₂ c w → ∀ y z, L₁.IsRho c j M g sig w y z → (y, z) ∈ Zf₁) →
    (∀ κ ∈ Zf₂, ∃ Y : Ext L₂ L₀, Y.Rep e₀ κ.1 κ.2 ∧ Y.Good e₀ Cu abelian₂ j M g rr) →
    rr ≤ 2 * a₀ →
    (∀ c ∈ Cu.cuts, ArcHyp h c (Cu.ell c) (abelian₂ c) g sig rr a₀ kap ϖ) →
    ∀ κ ∈ Zf₂, ∃ κ₁ ∈ Zf₁,
      L₂.IsCobound (B.lc ^ (2 * rr + 4 * sig + 2 * a₀ + 2 * kap) • κ.1 - fun i => h.f (κ₁.1 i))
        (B.lc ^ (2 * rr + 4 * sig + 2 * a₀ + 2 * kap) • κ.2 - fun i => h.f (κ₁.2 i))

end Formalism.ExponentWindows.E
