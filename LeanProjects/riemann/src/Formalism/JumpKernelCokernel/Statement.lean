import Mathlib
import Formalism.TruncatedSeriesCounting.RamifiedValuationInequality
import Formalism.TruncatedSeriesCounting.LengthQuotientLeOfPowSMul

noncomputable section

namespace Formalism.KernelCokernelLengths

open Polynomial

def RelZero : Prop :=
  ∀ (R : Type) [CommRing R] (u π₀ q : R) (ℓ h η y : ℕ), 2 ≤ ℓ → η ≤ h → h / (ℓ - 1) + 1 ≤ y →
    (u * π₀ * q ^ (ℓ - 1)) ^ y ∈ Ideal.span {π₀ ^ (h / (ℓ - 1) + 1) * q ^ η}

def PowBinom : Prop :=
  ∀ (A : Type) [CommRing A] (ℓ : ℕ) (u ε q : A) (b Y : ℕ), 1 ≤ ℓ → 1 ≤ Y →
    ∃ α β : A, (u * q ^ ℓ + (ℓ : A) * ε) ^ b = (ℓ : A) ^ (b - (Y - 1) / ℓ) * α + q ^ Y * β ∧
      β ∈ Ideal.span {(ℓ : A), q ^ ℓ} ^ (b - (Y - 1) / ℓ - 1)

def InvConst : Prop :=
  ∀ (K : Type) [Field K] (D : Type) [AddCommGroup D] [Module K D] (Fil : ℤ → Submodule K D),
    Antitone Fil → ∀ χ : K, (∀ i : ℤ, i ≠ 0 → χ ^ i ≠ 1) →
    ∀ (b η : ℕ) (w : ℤ → D),
      (∀ j : ℤ, -(b : ℤ) < j → j < -(η : ℤ) → Fil j = Fil (j + 1)) →
      (∀ i : ℤ, (χ ^ i - 1) • w i ∈ Fil (-i)) →
      (∀ i : ℤ, i ≠ 0 → w i ∈ Fil (-i)) ∧
        ∀ i : ℤ, i ≠ 0 → i < (b : ℤ) → w i ∈ Fil (-(η : ℤ))

def KerCoker : Prop :=
  ∀ (O : Type) [CommRing O] (M : Type) [AddCommGroup M] [Module O M], Module.length O M ≠ ⊤ →
    ∀ (f : Module.End O M) (N : Submodule O M), N.map f ≤ N →
      Module.length O (↥N ⧸ (N.map f).comap N.subtype) ≤ Module.length O (LinearMap.ker f)

def TorsKer : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ℓ : O), ℓ ≠ 0 →
    ∀ n k : ℕ,
      Module.length O (LinearMap.ker (LinearMap.mulLeft O
        (Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries O) ^ n, PowerSeries.C (ℓ ^ k)})
          ((PowerSeries.X : PowerSeries O) - PowerSeries.C ℓ)))) ≤
        (k : ℕ∞) * Module.length O (O ⧸ Ideal.span {ℓ})

def DetLen : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (M : Type) [AddCommGroup M]
    [Module O M] [Module.Free O M] [Module.Finite O M] (d : Module.End O M),
    LinearMap.det d ≠ 0 →
      Module.length O (M ⧸ LinearMap.range d) = Module.length O (O ⧸ Ideal.span {LinearMap.det d})

def CDge : Prop :=
  ∀ (ℓ : ℕ), 2 ≤ ℓ → ∀ (bi S η h : ℕ), bi + S ≤ h →
    (((bi + S + η : ℕ) : ℝ) + 1) / ((ℓ : ℝ) - 1) + 1 ≤ (((h + η : ℕ) : ℝ) + 1) / ((ℓ : ℝ) - 1) + 1

def ColThmC : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsPrincipalIdealRing O] (M : Type) [AddCommGroup M]
    [Module O M] [Module.Free O M] [Module.Finite O M] (ℓ : O) (P : Submodule O M) (k : ℕ)
    (F : ℕ → Submodule O M) (gen : Finset ℕ) (n r m e e' S cD : ℕ),
    Even n → Module.finrank O M ≤ (n + 1) * r → gen.card ≤ 4 * n → k - gen.card ≤ 3 * n / 2 →
    F 0 = ⊤ → (∀ i < k, F (i + 1) ≤ F i) → gen ⊆ Finset.range k →
    (∀ i ∈ gen, (∃ s : Finset M, s.card ≤ m ∧ (↑s : Set M) ⊆ F i ∧
        F i ≤ Submodule.span O (↑s : Set M) ⊔ F (i + 1)) ∧
      ∀ x ∈ F i, ℓ ^ e' • x ∈ F (i + 1) ⊔ P) →
    (∀ i < k, i ∉ gen →
      Module.length O (↥(F i) ⧸ (F (i + 1) ⊔ P).comap (F i).subtype) ≤
        ((r * S + 2 * m * cD : ℕ) : ℕ∞) * Module.length O (O ⧸ Ideal.span {ℓ})) →
    (∀ x ∈ F k, ℓ ^ e • x ∈ P) →
    Module.length O (M ⧸ P) ≤
      (((n + 1) * r * e + 4 * n * m * e' + (3 * n / 2) * (r * S + 2 * m * cD) : ℕ) : ℕ∞) *
        Module.length O (O ⧸ Ideal.span {ℓ})

def hCoef (x : ℝ) : ℝ := x ^ 2 * (8 * (2 * x - 1) / (x - 1) ^ 3 + 8 / (x - 1) ^ 2 + 1 / (x * (x - 1)))

def HCoefLim : Prop :=
  AntitoneOn hCoef (Set.Ici 11) ∧ (∀ x : ℝ, 11 ≤ x → 25 ≤ hCoef x) ∧
    Filter.Tendsto hCoef Filter.atTop (nhds 25)

def ThickA : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∃ B₀ : ℕ, ∀ ℓ : ℕ, 11 ≤ ℓ → ∀ (b η S t bi h : ℕ), B₀ ≤ b →
    (η : ℝ) ≤ δ * b → (S : ℝ) ≤ δ * b → (t : ℝ) ≤ δ * b →
    b ≤ bi + t + 1 → bi + S ≤ h → h ≤ b + η + t + S + 1 →
    ((2 * ⌈Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.aR ℓ (h + (η + t + 1))⌉₊ + (η + t + 1) + 1 : ℕ) : ℝ) ≤ (0.42 + ε) * b

def ThickB : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ ∃ B₀ : ℕ, ∀ ℓ : ℕ, 11 ≤ ℓ → ∀ (b η S t bi h : ℕ), B₀ ≤ b →
    (η : ℝ) ≤ δ * b → (S : ℝ) ≤ δ * b → (t : ℝ) ≤ δ * b →
    b ≤ bi + t + 1 → bi + S ≤ h → h ≤ b + η + t + S + 1 →
    2 * (η + t + 1) ≤ h ∧ h ≤ 2 * bi ∧
      2 * ⌈Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.aR ℓ (h + (η + t + 1))⌉₊ + (η + t + 1) + 1 ≤ bi

def RowD : Prop :=
  ∀ (ℓ h η : ℕ), 2 * η ≤ h → 32 * ((h + η : ℕ) : ℝ) / (ℓ : ℝ) ^ 2 ≤ 50 * (h : ℝ) / (ℓ : ℝ) ^ 2

def ExpRowD : Prop :=
  ∀ (ℓ : ℕ), 11 ≤ ℓ → ∀ (h η S b a : ℕ) (s₁ E e₂ : ℝ),
    2 * η ≤ h → b ≤ h → (a : ℝ) ≤ Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.aR ℓ (h + η) + 1 →
    s₁ ≤ (2 * (a : ℝ) + 2 * (η : ℝ) + (S : ℝ)) / ((ℓ : ℝ) - 1) + 2 * Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.lam ℓ (h + η) →
    E ≤ (3 * (a : ℝ) + (S : ℝ) + 2 * (η : ℝ)) / ((ℓ : ℝ) - 1) + 3 * Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.lam ℓ (h + η) →
    e₂ ≤ (b : ℝ) / ((ℓ : ℝ) * ((ℓ : ℝ) - 1)) + E + 2 * Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.sig₂ ℓ (h + η) + 2 * (S : ℝ) + 5
        + Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.lam ℓ (h + η) →
    s₁ + 2 * Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.sig ℓ h η + e₂ + (S : ℝ) + E + Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.sig₂ ℓ (h + η) ≤
      50 * (h : ℝ) / (ℓ : ℝ) ^ 2 + 4 * (S : ℝ) + 10 * (η : ℝ) / ((ℓ : ℝ) - 1)
        + 24 * Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.lam ℓ (h + η)

def QPow : Prop :=
  ∀ (R : Type) [CommRing R] (π₀ ℓ : R) (A r : ℕ), (π₀ + ℓ) ^ (A + r - 1) ∈ Ideal.span {π₀ ^ A, ℓ ^ r}

def FExp : Prop :=
  ∀ (R : Type) [CommRing R] (u π₀ q : R) (ℓ : ℕ), 2 ≤ ℓ → ∀ (Mi h : ℕ), Mi ≤ h →
    (u * π₀ * q ^ (ℓ - 1)) ^ (h / (ℓ - 1) + 1) ∈ Ideal.span {π₀ ^ (h / (ℓ - 1) + 1) * q ^ (Mi + 1)}

def LenSplit : Prop :=
  ∀ (O : Type) [CommRing O] (R : Type) [AddCommGroup R] [Module O R] (π : Module.End O R)
    (R' R'' : Submodule O R), R' ≤ R'' →
      Module.length O (R ⧸ (R' ⊔ LinearMap.range π)) ≤
        Module.length O (R ⧸ (R'' ⊔ LinearMap.range π)) +
          Module.length O (↥R'' ⧸ (R' ⊔ R''.map π).comap R''.subtype)

def JumpShift : Prop :=
  ∀ (s S η t a : ℤ), 0 ≤ t →
    (s ≤ a → a ≤ s + S → -(s + 1) - S ≤ -a - 1 ∧ -a - 1 ≤ -(s + 1)) ∧
    (-s - S ≤ a → a ≤ -s → s - 1 ≤ -a - 1 ∧ -a - 1 ≤ (s - 1) + S) ∧
    (-η ≤ a → a ≤ η → |-a - 1| ≤ η + t + 1) ∧
    (0 ≤ a → a ≤ t - 1 → 0 ≤ η → |-a - 1| ≤ η + t + 1)

def TorsKerSum : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ℓ : O), ℓ ≠ 0 →
    ∀ (m k : ℕ) (n : Fin m → ℕ),
      Module.length O (LinearMap.ker (LinearMap.pi (fun j : Fin m =>
        (LinearMap.mulLeft O
          (Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries O) ^ n j, PowerSeries.C (ℓ ^ k)})
            ((PowerSeries.X : PowerSeries O) - PowerSeries.C ℓ))).comp
          (LinearMap.proj (R := O) (φ := fun j : Fin m =>
            PowerSeries O ⧸ Ideal.span {(PowerSeries.X : PowerSeries O) ^ n j, PowerSeries.C (ℓ ^ k)}) j)))) ≤
        ((m * k : ℕ) : ℕ∞) * Module.length O (O ⧸ Ideal.span {ℓ})

def PdFacts : Prop :=
  ∀ (O : Type) [CommRing O] (V : Type) [AddCommGroup V] [Module O V] (d : Module.End O V)
    (P : O[X]) (M : Submodule O V), M.map d ≤ M →
    (aeval d (X * P) = 0 →
      (∀ v : V, d (aeval d P v) = 0) ∧ (∀ v : V, d v = 0 → aeval d P v = P.eval 0 • v) ∧
      ∀ w ∈ M, ∀ u : V, d u = w → P.eval 0 • w ∈ M.map d) ∧
    (aeval d P = 0 → ∀ u : V, d u ∈ M → P.eval 0 • u ∈ M)

def CokerTors : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (M : Type) [AddCommGroup M]
    [Module O M] [Module.Free O M] [Module.Finite O M] (d : Module.End O M) (k : ℕ) (Q : O[X]),
    Q.eval 0 ≠ 0 → LinearMap.charpoly d = X ^ k * Q → aeval d (X * Q) = 0 →
      Module.length O (Submodule.torsion O (M ⧸ LinearMap.range d)) ≤
        Module.length O (O ⧸ Ideal.span {Q.eval 0})

end Formalism.KernelCokernelLengths
