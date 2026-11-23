import Formalism.LagrangeIdealLifts.Statement
import Formalism.CoboundaryTransfers.Statement

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.N2

open Polynomial

def lagE (ℓ sg : ℕ) (S₁ S₂ : Finset ℤ) : ℕ :=
  S₁.sup fun a => (∑ b ∈ S₂, (sg + padicValInt ℓ (a - b))) +
    ∑ b ∈ S₁.erase a, (sg + padicValInt ℓ (a - b))

def StatLagrange : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (O : Type) [CommRing O] [IsDomain O] (S₁ S₂ : Finset ℤ) (c : ℤ → O)
    (sg : ℕ), Disjoint S₁ S₂ →
    (∀ a ∈ S₁ ∪ S₂, ∀ b ∈ S₁ ∪ S₂, a ≠ b →
      Associated (c a - c b) ((ℓ : O) ^ (sg + padicValInt ℓ (a - b)))) →
    C ((ℓ : O) ^ lagE ℓ sg S₁ S₂) ∈
      Ideal.span ({∏ a ∈ S₁, (X - C (c a)), ∏ b ∈ S₂, (X - C (c b))} : Set O[X])

def StatLagrangeKill : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (O : Type) [CommRing O] [IsDomain O] (S₁ S₂ : Finset ℤ) (c : ℤ → O)
    (sg : ℕ) (P : Type) [AddCommGroup P] [Module O P] (g : P →ₗ[O] P), Disjoint S₁ S₂ →
    (∀ a ∈ S₁ ∪ S₂, ∀ b ∈ S₁ ∪ S₂, a ≠ b →
      Associated (c a - c b) ((ℓ : O) ^ (sg + padicValInt ℓ (a - b)))) →
    aeval g (∏ a ∈ S₁, (X - C (c a))) = 0 → aeval g (∏ b ∈ S₂, (X - C (c b))) = 0 →
    ∀ x : P, ((ℓ : O) ^ lagE ℓ sg S₁ S₂) • x = 0

def StatSumValEnd : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (m : ℤ) (y D : ℕ) (S : Finset ℤ) (a : ℤ),
    S ⊆ Finset.Icc m (m + y) → (a ≤ m ∨ m + y ≤ a) → 1 ≤ D → (∀ b ∈ S, |a - b| ≤ D) →
    ((∑ b ∈ S.erase a, padicValInt ℓ (a - b) : ℕ) : ℝ) ≤
      ((y : ℝ) + 1) / ((ℓ : ℝ) - 1) + Real.logb ℓ D

def StatSumValGen : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (m : ℤ) (y D : ℕ) (S : Finset ℤ) (a : ℤ),
    S ⊆ Finset.Icc m (m + y) → 1 ≤ D → (∀ b ∈ S, |a - b| ≤ D) →
    ((∑ b ∈ S.erase a, padicValInt ℓ (a - b) : ℕ) : ℝ) ≤
      2 * (((y : ℝ) + 1) / ((ℓ : ℝ) - 1) + Real.logb ℓ D)

structure GBase (ℓ : ℕ) [Fact ℓ.Prime] (A : Type) [CommRing A] [Algebra ℤ_[ℓ] A] where
  γ : A →ₐ[ℤ_[ℓ]] A
  X : A
  u : ℤ_[ℓ]ˣ
  γX : ∃ t : A, γ X = X * (algebraMap ℤ_[ℓ] A (u : ℤ_[ℓ]) + X * t)

variable {ℓ : ℕ} [Fact ℓ.Prime] {A : Type} [CommRing A] [Algebra ℤ_[ℓ] A]

structure GPair (G : GBase ℓ A) (D : Type) [AddCommGroup D] [Module A D] [Module ℤ_[ℓ] D]
    [IsScalarTower ℤ_[ℓ] A D] where
  N : Submodule A D
  N' : Submodule A D
  le : N' ≤ N
  γ : D →ₗ[ℤ_[ℓ]] D
  γ_smul : ∀ (a : A) (x : D), γ (a • x) = G.γ a • γ x
  X_inj : ∀ x : D, G.X • x = 0 → x = 0
  γ_N : ∀ x ∈ N, ∃ x' ∈ N, γ x - x = G.X • x'
  γ_N' : ∀ x ∈ N', ∃ x' ∈ N', γ x - x = G.X • x'

def GPair.Kills {G : GBase ℓ A} {D : Type} [AddCommGroup D] [Module A D] [Module ℤ_[ℓ] D]
    [IsScalarTower ℤ_[ℓ] A D] (P : GPair G D) (a : A) : Prop := ∀ n ∈ P.N, a • n ∈ P.N'

def eWB (ℓ H s : ℕ) : ℕ := 2 * H * s + padicValNat ℓ (2 * H).factorial

def eWA (ℓ H : ℕ) : ℕ :=
  ⌊(H : ℝ) * ℓ / ((ℓ : ℝ) - 1) ^ 2 + 3 + Real.logb ℓ ((H : ℝ) + 1)⌋₊

def StatWB : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (A : Type) [CommRing A] [Algebra ℤ_[ℓ] A] (G : GBase ℓ A)
    (D : Type) [AddCommGroup D] [Module A D] [Module ℤ_[ℓ] D] [IsScalarTower ℤ_[ℓ] A D]
    (P : GPair G D) (s H : ℕ),
    1 ≤ s → (ℓ = 2 → 2 ≤ s) → PadicInt.valuation ((G.u : ℤ_[ℓ]) - 1) = s →
    P.Kills (G.X ^ H) → P.Kills ((ℓ : A) ^ eWB ℓ H s)

def IsGen (ℓ : ℕ) [Fact ℓ.Prime] (χ : ℤ_[ℓ]ˣ) : Prop :=
  (∀ k : ℕ, (ℓ : ℤ_[ℓ]) ∣ (χ : ℤ_[ℓ]) ^ k - 1 → (ℓ - 1) ∣ k) ∧
    PadicInt.valuation ((χ : ℤ_[ℓ]) ^ (ℓ - 1) - 1) = 1

def StatChiVal : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime], ℓ ≠ 2 → ∀ χ : ℤ_[ℓ]ˣ, IsGen ℓ χ → ∀ k : ℕ, 1 ≤ k →
    (χ : ℤ_[ℓ]) ^ k - 1 ≠ 0 ∧
    PadicInt.valuation ((χ : ℤ_[ℓ]) ^ k - 1) = if (ℓ - 1) ∣ k then 1 + padicValNat ℓ k else 0

def StatDescentStep : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (A : Type) [CommRing A] [Algebra ℤ_[ℓ] A] (G : GBase ℓ A)
    (D : Type) [AddCommGroup D] [Module A D] [Module ℤ_[ℓ] D] [IsScalarTower ℤ_[ℓ] A D]
    (P : GPair G D) (c : ℤ_[ℓ]) (j : ℕ),
    P.Kills (algebraMap ℤ_[ℓ] A c * G.X ^ (j + 1)) →
    P.Kills (algebraMap ℤ_[ℓ] A (c * ((G.u : ℤ_[ℓ]) ^ (j + 1) - 1)) * G.X ^ j)

def StatDescent : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (A : Type) [CommRing A] [Algebra ℤ_[ℓ] A] (G : GBase ℓ A)
    (D : Type) [AddCommGroup D] [Module A D] [Module ℤ_[ℓ] D] [IsScalarTower ℤ_[ℓ] A D]
    (P : GPair G D) (s j : ℕ), j ≤ s → P.Kills (G.X ^ s) →
    P.Kills (algebraMap ℤ_[ℓ] A (∏ k ∈ Finset.Ioc j s, ((G.u : ℤ_[ℓ]) ^ k - 1)) * G.X ^ j)

def cost (ℓ j s : ℕ) : ℕ :=
  ∑ k ∈ Finset.Ioc j s, if (ℓ - 1) ∣ k then 1 + padicValNat ℓ k else 0

def cW (ℓ H : ℕ) : ℕ := ⌈1 + Real.logb ℓ ((H : ℝ) + 1)⌉₊

def StatCostFormula : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime], ℓ ≠ 2 → ∀ j s : ℕ, j ≤ s →
    cost ℓ j s + padicValNat ℓ (j / (ℓ - 1)).factorial =
      (s / (ℓ - 1) - j / (ℓ - 1)) + padicValNat ℓ (s / (ℓ - 1)).factorial

def StatCostBound : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime], ℓ ≠ 2 → ∀ j s H : ℕ, j ≤ s → s ≤ H →
    (cost ℓ j s : ℝ) <
      ((s : ℝ) - j) * ℓ / ((ℓ : ℝ) - 1) ^ 2 + 1 + Real.logb ℓ ((H : ℝ) + 1)

def StatCostKills : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime], ℓ ≠ 2 → ∀ (A : Type) [CommRing A] [Algebra ℤ_[ℓ] A] (G : GBase ℓ A)
    (D : Type) [AddCommGroup D] [Module A D] [Module ℤ_[ℓ] D] [IsScalarTower ℤ_[ℓ] A D]
    (P : GPair G D) (s j : ℕ), IsGen ℓ G.u → j ≤ s → P.Kills (G.X ^ s) →
    P.Kills ((ℓ : A) ^ cost ℓ j s * G.X ^ j)

def Stat1 : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime], ℓ ≠ 2 → ∀ (A : Type) [CommRing A] [Algebra ℤ_[ℓ] A] (G : GBase ℓ A)
    (D : Type) [AddCommGroup D] [Module A D] [Module ℤ_[ℓ] D] [IsScalarTower ℤ_[ℓ] A D]
    (P : GPair G D) (s H a j : ℕ), IsGen ℓ G.u → s ≤ H → P.Kills (G.X ^ s) →
    ((s : ℝ) - j) * ℓ / ((ℓ : ℝ) - 1) ^ 2 + cW ℓ H ≤ a →
    P.Kills ((ℓ : A) ^ a * G.X ^ j)

def StatWA : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime], ℓ ≠ 2 → ∀ (A : Type) [CommRing A] [Algebra ℤ_[ℓ] A] (G : GBase ℓ A)
    (D : Type) [AddCommGroup D] [Module A D] [Module ℤ_[ℓ] D] [IsScalarTower ℤ_[ℓ] A D]
    (P : GPair G D) (H : ℕ), IsGen ℓ G.u → P.Kills (G.X ^ H) → P.Kills ((ℓ : A) ^ eWA ℓ H)

def StatWA0 : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime], ℓ ≠ 2 → ∀ (A : Type) [CommRing A] [Algebra ℤ_[ℓ] A] (G : GBase ℓ A)
    (D : Type) [AddCommGroup D] [Module A D] [Module ℤ_[ℓ] D] [IsScalarTower ℤ_[ℓ] A D]
    (P : GPair G D) (H : ℕ), PadicInt.valuation ((G.u : ℤ_[ℓ]) - 1) = 1 →
    P.Kills (G.X ^ ((H + (ℓ - 2)) / (ℓ - 1))) →
    P.Kills ((ℓ : A) ^ ((H + (ℓ - 2)) / (ℓ - 1) +
      padicValNat ℓ ((H + (ℓ - 2)) / (ℓ - 1)).factorial)) ∧ P.Kills ((ℓ : A) ^ eWA ℓ H)

structure PhiStep (ℓ : ℕ) (A : Type) [CommRing A] (D D' : Type) [AddCommGroup D] [Module A D]
    [AddCommGroup D'] [Module A D'] where
  φA : A →+* A
  π : A
  q : A
  w : A
  φπ : φA π = π * q
  hq : q = (ℓ : A) * w + π ^ (ℓ - 1)
  φ : D →+ D'
  φ_smul : ∀ (a : A) (x : D), φ (a • x) = φA a • φ x
  P : Submodule A D
  P' : Submodule A D
  R : Submodule A D'
  R' : Submodule A D'

def Stat2Free : Prop :=
  ∀ (ℓ : ℕ) (A : Type) [CommRing A] (D D' : Type) [AddCommGroup D] [Module A D]
    [AddCommGroup D'] [Module A D'] (S : PhiStep ℓ A D D'), S.P' ≤ S.P →
    (∀ g : A, ∃ e : Fin ℓ → A, g = ∑ k : Fin ℓ, S.π ^ (k : ℕ) * S.φA (e k)) → 1 ≤ ℓ →
    (∀ x : Fin ℓ → D, (∀ k, x k ∈ S.P) → ∑ k : Fin ℓ, S.π ^ (k : ℕ) • S.φ (x k) = 0 →
      ∀ k, x k = 0) →
    ∀ x ∈ S.P, S.φ x ∈ Submodule.span A (S.φ '' (S.P' : Set D)) → x ∈ S.P'

def Stat2 : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime], ℓ ≠ 2 → ∀ (A : Type) [CommRing A] (D D' : Type) [AddCommGroup D]
    [Module A D] [AddCommGroup D'] [Module A D'] (S : PhiStep ℓ A D D') (Mi hi s H : ℕ),
    (∀ n ∈ S.P, S.q ^ Mi • S.φ n ∈ S.R) →
    (∀ r ∈ S.R', S.q ^ hi • r ∈ Submodule.span A (S.φ '' (S.P' : Set D))) →
    (∀ x ∈ S.P, S.φ x ∈ Submodule.span A (S.φ '' (S.P' : Set D)) → x ∈ S.P') →
    (∀ r ∈ S.R, S.π ^ s • r ∈ S.R') →
    (∀ a j : ℕ, ((s : ℝ) - j) * ℓ / ((ℓ : ℝ) - 1) ^ 2 + cW ℓ H ≤ a →
      ∀ r ∈ S.R, ((ℓ : A) ^ a * S.π ^ j) • r ∈ S.R') →
    ∀ n ∈ S.P, S.π ^ (Mi + hi + cW ℓ H + 2 + (s + (ℓ - 2)) / (ℓ - 1)) • n ∈ S.P'

def StatResFinite : Prop :=
  ∀ (n : ℕ) [NeZero n] (ℓ c : ℝ) (s H : ZMod n → ℝ), 1 < ℓ →
    (∀ k, s (k - 1) ≤ H k + c + 3 + s k / (ℓ - 1)) →
    ∀ (i : ZMod n) (m : ℕ),
      s i ≤ (∑ a ∈ Finset.range m, (H (i + ((a + 1 : ℕ) : ZMod n)) + c + 3) / (ℓ - 1) ^ a) +
        s (i + (m : ZMod n)) / (ℓ - 1) ^ m

def StatResSeries : Prop :=
  ∀ (n : ℕ) [NeZero n] (ℓ c : ℝ) (s H : ZMod n → ℝ), 3 ≤ ℓ → 0 ≤ c → (∀ k, 0 ≤ H k) →
    (∀ k, s (k - 1) ≤ H k + c + 3 + s k / (ℓ - 1)) →
    ∀ i : ZMod n, s i ≤ ∑' a : ℕ, (H (i + ((a + 1 : ℕ) : ZMod n)) + c + 3) / (ℓ - 1) ^ a

def StatResAlways : Prop :=
  ∀ (ℓ s H : ℕ) (c r : ℝ), 3 ≤ ℓ → s ≤ H → r ≤ (s : ℝ) * ℓ / ((ℓ : ℝ) - 1) ^ 2 + c →
    (((s + (ℓ - 2)) / (ℓ - 1) : ℕ) : ℝ) ≤ (H : ℝ) / ((ℓ : ℝ) - 1) + 1 ∧
    (((s + (ℓ - 2)) / (ℓ - 1) : ℕ) : ℝ) + r ≤
      (H : ℝ) * (2 * ℓ - 1) / ((ℓ : ℝ) - 1) ^ 2 + c + 1

def StatResQ : Prop :=
  ∀ (A : Type) [CommRing A] (D : Type) [AddCommGroup D] [Module A D] (N N' : Submodule A D)
    (π₀ : A) (ℓ a r : ℕ), (∀ n ∈ N, π₀ ^ a • n ∈ N') → (∀ n ∈ N, (ℓ : A) ^ r • n ∈ N') →
    ∀ n ∈ N, (π₀ + (ℓ : A)) ^ (a + r) • n ∈ N'

def StatResCut : Prop :=
  ∀ (n : ℕ) [NeZero n] (ℓ c G Hm : ℝ) (s H : ZMod n → ℝ) (i : ZMod n) (j : ℕ),
    3 ≤ ℓ → 0 ≤ c → 0 ≤ G → (∀ k, s k ≤ Hm) →
    (∀ k : ℕ, 1 ≤ k → k ≤ j → H (i + (k : ZMod n)) ≤ 2 * G) →
    (∀ k, s (k - 1) ≤ H k + c + 3 + s k / (ℓ - 1)) →
    s i ≤ (2 * G + c + 3) * (ℓ - 1) / (ℓ - 2) + Hm / (ℓ - 1) ^ j

def aH (ℓ r : ℕ) : ℕ := r + padicValNat ℓ r.factorial

def StatASuper : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (r s : ℕ), aH ℓ r + aH ℓ s ≤ aH ℓ (r + s)

def StatFrameInv : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [Ring E] (I : Subring E) (Cf Cf' : ℕ → E),
    Cf 0 = 1 → Cf' 0 = 1 → (∀ r, (ℓ : E) ^ aH ℓ r * Cf r ∈ I) →
    (∀ r, 1 ≤ r → ∑ p ∈ Finset.HasAntidiagonal.antidiagonal r, Cf p.1 * Cf' p.2 = 0) →
    ∀ r, (ℓ : E) ^ aH ℓ r * Cf' r ∈ I

def StatSigJ : Prop :=
  ∀ (A : Type) [CommRing A] (ℓ : ℕ), 2 ≤ ℓ → ∀ (x U : A) (p : ℕ → A) (j y r c : ℕ), 1 ≤ j → 1 ≤ r →
    (∀ k < j, p k ∈ Ideal.span {(ℓ : A), (x + (ℓ : A)) ^ (ℓ ^ k)}) →
    c * ℓ ^ (j - 1) + y ≤ r * ℓ ^ j →
    (U * x * ∏ k ∈ Finset.range j, p k ^ (ℓ - 1)) ^ r ∈
      Ideal.span {(ℓ : A) ^ c * x, x * (x + (ℓ : A)) ^ y}

def StatSigJNum : Prop :=
  ∀ (ℓ : ℕ), 3 ≤ ℓ → ∀ (j y r : ℕ), 1 ≤ j →
    (r : ℝ) * ℓ / ((ℓ : ℝ) - 1) - max 0 ((ℓ : ℝ) * r - (y : ℝ) / (ℓ : ℝ) ^ (j - 1)) ≤
      (y : ℝ) / ((ℓ : ℝ) ^ (j - 1) * ((ℓ : ℝ) - 1))

end Formalism.RepresentationBoundsCohomology.N2
