import Mathlib

noncomputable section

namespace Formalism.ExponentWindows

def cst {O : Type} [CommRing O] {r : ℕ} (v : Fin r → O) : Fin r → PowerSeries O :=
  fun i => PowerSeries.C (v i)

def ext {O : Type} [CommRing O] {r : ℕ} (V : Submodule O (Fin r → O)) :
    Submodule (PowerSeries O) (Fin r → PowerSeries O) :=
  Submodule.span (PowerSeries O) (cst '' (V : Set (Fin r → O)))

def Saturated {O : Type} [CommRing O] {r : ℕ} (ϖ : O) (V : Submodule O (Fin r → O)) : Prop :=
  ∀ v : Fin r → O, ϖ • v ∈ V → v ∈ V

inductive Kind where
  | thin
  | up
  | down
  deriving DecidableEq

def UnitDist {O : Type} [CommRing O] (ϖ : O) (d : ℕ) (p : PowerSeries O) : Prop :=
  ∃ (u : PowerSeries O) (E : Polynomial O), IsUnit u ∧ E.IsDistinguishedAt (Ideal.span {ϖ}) ∧
    E.natDegree = d ∧ p = u * (E : PowerSeries O)

def CoprimeRat {O : Type} [CommRing O] (ϖ : O) (p p' : PowerSeries O) : Prop :=
  ∃ (N : ℕ) (a a' : PowerSeries O), a * p + a' * p' = PowerSeries.C (ϖ ^ N)

def DistinguishedFamily {O : Type} [CommRing O] (ϖ : O) (ℓ ell : ℕ) (p : ℕ → PowerSeries O) : Prop :=
  (∀ s < ell, UnitDist ϖ (ℓ ^ s) (p s)) ∧
    (∀ s < ell, ∀ s' < ell, s ≠ s' → CoprimeRat ϖ (p s) (p s'))

def LevelCond {O : Type} [CommRing O] {r : ℕ} (ϖ : O) (p : PowerSeries O) (H b : ℕ) (k : Kind)
    (V : Submodule O (Fin r → O)) (y : Fin r → PowerSeries O) : Prop :=
  match k with
  | Kind.thin => ∃ (N : ℕ) (z : Fin r → PowerSeries O), PowerSeries.C (ϖ ^ N) • y = p ^ H • z
  | Kind.up => ∃ (N : ℕ) (c z : Fin r → PowerSeries O), c ∈ ext V ∧
      PowerSeries.C (ϖ ^ N) • y = p ^ (H - b) • c + p ^ H • z
  | Kind.down => ∃ (N : ℕ) (c z : Fin r → PowerSeries O), c ∈ ext V ∧
      PowerSeries.C (ϖ ^ N) • y = p ^ H • c + p ^ (H + b) • z

def abelian₂ {O : Type} [CommRing O] (p : ℕ → PowerSeries O) (H : ℕ → ℕ) (ell : ℕ) : PowerSeries O :=
  ∏ s ∈ Finset.range ell, p s ^ H s

def LamLess {O : Type} [CommRing O] (p : ℕ → PowerSeries O) (H : ℕ → ℕ) (ell s₁ b : ℕ) :
    PowerSeries O :=
  p s₁ ^ (H s₁ - b) * ∏ s ∈ (Finset.range ell).erase s₁, p s ^ H s

def NN {O : Type} [CommRing O] {r : ℕ} (ϖ : O) (p : ℕ → PowerSeries O) (H b : ℕ → ℕ)
    (kind : ℕ → Kind) (V : ℕ → Submodule O (Fin r → O)) (ell : ℕ) (y : Fin r → PowerSeries O) :
    Prop :=
  ∀ s < ell, LevelCond ϖ (p s) (H s) (b s) (kind s) (V s) y

def II {O : Type} [CommRing O] {r : ℕ} (ϖ : O) (p : ℕ → PowerSeries O) (H b : ℕ → ℕ)
    (kind : ℕ → Kind) (V : ℕ → Submodule O (Fin r → O)) (ell : ℕ) (y : Fin r → PowerSeries O) :
    Prop :=
  ∀ s < ell, ∃ (d : Fin r → O) (k : ℕ),
    LevelCond ϖ (p s) (H s) (b s) (kind s) (V s) (PowerSeries.C (ϖ ^ k) • y - abelian₂ p H ell • cst d)

def MNone : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (ℓ ell r : ℕ) (p : ℕ → PowerSeries O) (H b : ℕ → ℕ) (kind : ℕ → Kind)
      (V : ℕ → Submodule O (Fin r → O)),
      2 ≤ ℓ → DistinguishedFamily ϖ ℓ ell p → (∀ s < ell, Saturated ϖ (V s)) →
      (∀ s < ell, kind s = Kind.up → b s ≤ H s) →
      (∀ s < ell, kind s ≠ Kind.down) →
      ∀ y : Fin r → PowerSeries O, II ϖ p H b kind V ell y ↔ NN ϖ p H b kind V ell y

def MD : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (ℓ ell r : ℕ) (p : ℕ → PowerSeries O) (H b : ℕ → ℕ) (kind : ℕ → Kind)
      (V : ℕ → Submodule O (Fin r → O)),
      2 ≤ ℓ → DistinguishedFamily ϖ ℓ ell p → (∀ s < ell, Saturated ϖ (V s)) →
      (∀ s < ell, kind s = Kind.up → b s ≤ H s) →
      ∀ s₁ : ℕ, s₁ < ell → kind s₁ = Kind.down → (∀ s < ell, s ≠ s₁ → kind s = Kind.thin) →
      ∀ y : Fin r → PowerSeries O, II ϖ p H b kind V ell y ↔
        ∃ (lam : Fin r → O) (ν : Fin r → PowerSeries O), NN ϖ p H b kind V ell ν ∧
          y = abelian₂ p H ell • cst lam + ν

def MDU : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (ℓ ell r : ℕ) (p : ℕ → PowerSeries O) (H b : ℕ → ℕ) (kind : ℕ → Kind)
      (V : ℕ → Submodule O (Fin r → O)),
      2 ≤ ℓ → DistinguishedFamily ϖ ℓ ell p → (∀ s < ell, Saturated ϖ (V s)) →
      (∀ s < ell, kind s = Kind.up → b s ≤ H s) →
      ∀ s₀ s₁ : ℕ, s₀ < s₁ → s₁ < ell → kind s₁ = Kind.down → kind s₀ = Kind.up →
      (∀ s < ell, s ≠ s₀ → s ≠ s₁ → kind s = Kind.thin) → b s₀ < ℓ * b s₁ →
      ∀ y : Fin r → PowerSeries O, II ϖ p H b kind V ell y ↔
        ∃ (lam : Fin r → O) (ν : Fin r → PowerSeries O), NN ϖ p H b kind V ell ν ∧
          y = abelian₂ p H ell • cst lam + ν

def MDD : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (ℓ ell r : ℕ) (p : ℕ → PowerSeries O) (H b : ℕ → ℕ) (kind : ℕ → Kind)
      (V : ℕ → Submodule O (Fin r → O)),
      2 ≤ ℓ → DistinguishedFamily ϖ ℓ ell p → (∀ s < ell, Saturated ϖ (V s)) →
      (∀ s < ell, kind s = Kind.up → b s ≤ H s) →
      ∀ s₀ s₁ : ℕ, s₀ < s₁ → s₁ < ell → kind s₁ = Kind.down → kind s₀ = Kind.down →
      (∀ s < ell, s ≠ s₀ → s ≠ s₁ → kind s = Kind.thin) →
      ∀ (ρ : ℕ) (fρ : PowerSeries O),
      PowerSeries.C (ϖ ^ ρ) ∈ Ideal.span {p s₁ ^ b s₁, p s₀ ^ b s₀} →
      (∀ k : ℕ, PowerSeries.C (ϖ ^ k) ∈ Ideal.span {p s₁ ^ b s₁, p s₀ ^ b s₀} → ρ ≤ k) →
      fρ ∈ Ideal.span {p s₁ ^ b s₁} → fρ - PowerSeries.C (ϖ ^ ρ) ∈ Ideal.span {p s₀ ^ b s₀} →
      ∀ y : Fin r → PowerSeries O, II ϖ p H b kind V ell y ↔
        ∃ (lam lam' : Fin r → O) (ν : Fin r → PowerSeries O), NN ϖ p H b kind V ell ν ∧
          y = abelian₂ p H ell • cst lam + (abelian₂ p H ell * fρ) • cst lam' + ν

def MUD : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (ℓ ell r : ℕ) (p : ℕ → PowerSeries O) (H b : ℕ → ℕ) (kind : ℕ → Kind)
      (V : ℕ → Submodule O (Fin r → O)),
      2 ≤ ℓ → DistinguishedFamily ϖ ℓ ell p → (∀ s < ell, Saturated ϖ (V s)) →
      (∀ s < ell, kind s = Kind.up → b s ≤ H s) →
      ∀ s₀ s₁ : ℕ, s₀ < s₁ → s₁ < ell → kind s₁ = Kind.up → kind s₀ = Kind.down →
      (∀ s < ell, s ≠ s₀ → s ≠ s₁ → kind s = Kind.thin) →
      ∀ (c : ℕ) (α β : PowerSeries O),
      p s₁ ^ b s₁ = PowerSeries.C (ϖ ^ c) * α + p s₀ ^ b s₀ * β →
      p s₁ ^ b s₁ ∉ Ideal.span {PowerSeries.C (ϖ ^ (c + 1)), p s₀ ^ b s₀} →
      ∀ y : Fin r → PowerSeries O, II ϖ p H b kind V ell y ↔
        ∃ (lam lam' : Fin r → O) (ν : Fin r → PowerSeries O), lam' ∈ V s₁ ∧
          NN ϖ p H b kind V ell ν ∧
          y = abelian₂ p H ell • cst lam + (α * LamLess p H ell s₁ (b s₁)) • cst lam' + ν

def DUConst : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (ℓ : ℕ) (p : ℕ → PowerSeries O) (I : Finset ℕ) (b : ℕ → ℕ) (g B y N : ℕ) (c : O)
      (a : PowerSeries O),
      (∀ s ∈ insert g I, UnitDist ϖ (ℓ ^ s) (p s)) →
      ∑ s ∈ I, b s * ℓ ^ s < B * ℓ ^ g →
      PowerSeries.C (ϖ ^ N) * (PowerSeries.C c * ∏ s ∈ I, p s ^ b s - PowerSeries.C (ϖ ^ y) * a) ∈
        Ideal.span {p g ^ B} →
      ϖ ^ y ∣ c

def KillerShift : Prop :=
  ∀ (R M : Type) [CommRing R] [AddCommGroup M] [Module R M] (γ : Module.End R M)
    (U : Submodule R M), (∀ u ∈ U, γ u ∈ U) →
    ∀ (P : Polynomial R) (w : M), γ w - w ∈ U → Polynomial.aeval γ P w - P.eval 1 • w ∈ U

def InvConst : Prop :=
  ∀ (k V : Type) [Field k] [AddCommGroup V] [Module k V] (γ : Module.End k V)
    (U : Submodule k V), (∀ u ∈ U, γ u ∈ U) →
    ∀ Q₀ : Polynomial k, Q₀.eval 1 ≠ 0 →
      (∀ v : V, Polynomial.aeval γ ((Polynomial.X - 1) * Q₀) v = 0) →
      ∀ w : V, γ w - w ∈ U → ∃ w₀ u : V, γ w₀ = w₀ ∧ u ∈ U ∧ w = w₀ + u

def CutPlace : Prop :=
  ∀ (n j : ℕ) [NeZero n] (thick : ZMod n → Prop) [DecidablePred thick], 1 ≤ j → j + 1 ≤ n →
    (∀ a : ZMod n, thick a → ∀ k : ℕ, 1 ≤ k → k ≤ j → thick (a - k) →
      ∀ k' : ℕ, 1 ≤ k' → k' ≤ j → ¬ thick (a - k - k')) →
    ∃ (cuts : Finset (ZMod n)) (ell : ZMod n → ℕ), cuts.Nonempty ∧
      ∀ c ∈ cuts,
        (∀ k : ℕ, 1 ≤ k → k ≤ j → ¬ thick (c + k)) ∧
        j ≤ ell c ∧ ell c ≤ 3 * j + 1 ∧ ell c ≤ n ∧
        c - (ell c : ZMod n) ∈ cuts ∧ (∀ k : ℕ, 1 ≤ k → k < ell c → c - k ∉ cuts) ∧
        (∀ k : ℕ, k < ell c → thick (c - k) → k ≤ j) ∧
        ((Finset.range (ell c)).filter (fun k : ℕ => thick (c - (k : ZMod n)))).card ≤ 2 ∧
        (∀ k k' : ℕ, k < ell c → k' < ell c → thick (c - k) → thick (c - k') →
          k ≤ k' + j ∧ k' ≤ k + j)

def LemmaCValR : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (ℓ e : ℕ), 2 ≤ ℓ → 1 ≤ e → Associated (ℓ : O) (ϖ ^ e) →
    ∀ (E : ℕ → Polynomial O) (u : ℕ → PowerSeries O),
      (∀ s, (E s).Monic) → (∀ s, (E s).natDegree = ℓ ^ s) →
      (∀ s, ∀ i < ℓ ^ s, (ℓ : O) ∣ (E s).coeff i) → (∀ s, Associated ((E s).coeff 0) (ℓ : O)) →
      (∀ s, IsUnit (u s)) →
      ∀ (ell g a b₀ b₁ s₀ s₁ k : ℕ), s₀ < s₁ →
        2 * ((a : ℝ) + 2 * g * ell) < b₁ → 2 * b₀ ≤ ℓ * b₁ →
        PowerSeries.C ((ℓ : O) ^ a) *
            (∏ s ∈ Finset.range ell, (u s * (E s : PowerSeries O)) ^ g) ^ 2 *
            (u s₀ * (E s₀ : PowerSeries O)) ^ b₀ ∈
          Ideal.span {PowerSeries.C (ϖ ^ k), (u s₁ * (E s₁ : PowerSeries O)) ^ b₁} →
        (k : ℝ) ≤ e * (((a : ℝ) + 2 * g * ell) * b₁ / (b₁ - b₀ / ℓ)) ∧
          (k : ℝ) ≤ 2 * e * ((a : ℝ) + 2 * g * ell)

end Formalism.ExponentWindows
