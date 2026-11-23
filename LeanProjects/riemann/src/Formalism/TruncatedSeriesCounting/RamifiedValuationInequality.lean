import Mathlib
import Formalism.WindowSums.Statement
import Formalism.FrobeniusContraction.Statement
import Formalism.LagrangeIdealLifts.Statement

noncomputable section

namespace Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains

open Polynomial

def lam (ℓ H : ℕ) : ℝ := Real.logb (ℓ : ℝ) (2 * (H : ℝ)) + 1

def aR (ℓ H : ℕ) : ℝ := (H : ℝ) * (2 * (ℓ : ℝ) - 1) / ((ℓ : ℝ) - 1) ^ 2 + 3 + lam ℓ H

def sig (ℓ h η : ℕ) : ℝ := (((h / (ℓ - 1) + 1 : ℕ) : ℝ) + (η : ℝ)) / ((ℓ : ℝ) - 1) + 1

def sig₂ (ℓ H : ℕ) : ℝ := 2 * (H : ℝ) / ((ℓ : ℝ) - 1) ^ 2 + 1

def HCoef : Prop :=
  ∀ x : ℝ, 11 ≤ x →
    8 * (2 * x - 1) / (x - 1) ^ 3 + 8 / (x - 1) ^ 2 + 1 / (x * (x - 1)) ≤ 32 / x ^ 2

def ExpBound : Prop :=
  ∀ (ℓ : ℕ), 11 ≤ ℓ → ∀ (h η S b a : ℕ) (s₁ E e₂ : ℝ),
    b ≤ h → (a : ℝ) ≤ aR ℓ (h + η) + 1 →
    s₁ ≤ (2 * (a : ℝ) + 2 * (η : ℝ) + (S : ℝ)) / ((ℓ : ℝ) - 1) + 2 * lam ℓ (h + η) →
    E ≤ (3 * (a : ℝ) + (S : ℝ) + 2 * (η : ℝ)) / ((ℓ : ℝ) - 1) + 3 * lam ℓ (h + η) →
    e₂ ≤ (b : ℝ) / ((ℓ : ℝ) * ((ℓ : ℝ) - 1)) + E + 2 * sig₂ ℓ (h + η) + 2 * (S : ℝ) + 5
        + lam ℓ (h + η) →
    s₁ + 2 * sig ℓ h η + e₂ + (S : ℝ) + E + sig₂ ℓ (h + η) ≤
      32 * ((h + η : ℕ) : ℝ) / (ℓ : ℝ) ^ 2 + 4 * (S : ℝ) + 10 * (η : ℝ) / ((ℓ : ℝ) - 1)
        + 24 * lam ℓ (h + η)

def MaxZeroExponentInequality : Prop :=
  ∀ (ℓ : ℕ), 2 ≤ ℓ → ∀ (b b' S h'' : ℕ) (E s₂ L c' : ℝ), 0 ≤ E → 0 ≤ s₂ → 0 ≤ L →
    c' ≤ (b' : ℝ) + (S : ℝ) - (b : ℝ) / (ℓ : ℝ) + 2 + L →
    max 0 ((((b + S + 1 : ℕ) : ℝ) / ((ℓ : ℝ) - 1) + 1 + E + s₂ + (h'' : ℝ) - (b' : ℝ))
        + s₂ + c' - (h'' : ℝ)) ≤
      (b : ℝ) / ((ℓ : ℝ) * ((ℓ : ℝ) - 1)) + E + 2 * s₂ + 2 * (S : ℝ) + 5 + L

def TwoIntervalValuationSumBound : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (h η S b a : ℕ), 2 * a + η + 1 ≤ b → b + S ≤ h →
    ((∑ j ∈ (Finset.Icc (1 - (η : ℤ)) ((η : ℤ) + a) ∪
          Finset.Icc (1 - ((b + S : ℕ) : ℤ)) ((a : ℤ) - b)).erase 0, padicValInt ℓ j : ℕ) : ℝ) ≤
      (2 * (a : ℝ) + 2 * (η : ℝ) + (S : ℝ)) / ((ℓ : ℝ) - 1) + 2 * lam ℓ (h + η)

def LemmaGVal : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (h η S b a : ℕ) (S₂ : Finset ℤ), 2 * a + η + 1 ≤ b → b + S ≤ h →
    S₂ ⊆ Finset.Icc ((b : ℤ) + 1) ((b : ℤ) + S + a) ∪ Finset.Icc (1 - (η : ℤ)) ((η : ℤ) + a) →
    ∀ j₀ ∈ Finset.Icc ((b : ℤ) - a + 1) (b : ℤ),
      (((∑ j ∈ (Finset.Icc ((b : ℤ) - a + 1) (b : ℤ)).erase j₀, padicValInt ℓ (j₀ - j)) +
          ∑ j ∈ S₂, padicValInt ℓ (j₀ - j) : ℕ) : ℝ) ≤
        (3 * (a : ℝ) + (S : ℝ) + 2 * (η : ℝ)) / ((ℓ : ℝ) - 1) + 3 * lam ℓ (h + η)

def LemmaGIdeal : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (R : Type) [CommRing R] [IsDomain R] (c : ℤ → R),
    (∀ j j' : ℤ, j ≠ j' → Associated (c j - c j') ((ℓ : R) ^ padicValInt ℓ (j - j'))) →
    ∀ (h η S b a : ℕ) (S₂ : Finset ℤ), 2 * a + η + 1 ≤ b → b + S ≤ h →
      S₂ ⊆ Finset.Icc ((b : ℤ) + 1) ((b : ℤ) + S + a) ∪ Finset.Icc (1 - (η : ℤ)) ((η : ℤ) + a) →
      ∃ E : ℕ, (E : ℝ) ≤ (3 * (a : ℝ) + (S : ℝ) + 2 * (η : ℝ)) / ((ℓ : ℝ) - 1) + 3 * lam ℓ (h + η) ∧
      Polynomial.C ((ℓ : R) ^ E) ∈
        Ideal.span ({∏ j ∈ Finset.Icc ((b : ℤ) - a + 1) (b : ℤ), (X - C (c j)),
          ∏ j ∈ S₂, (X - C (c j))} : Set (Polynomial R))

def RamifiedValuationInequality : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ℓ : ℕ) [Fact ℓ.Prime]
    (ϖ : O) (e : ℕ), Irreducible ϖ → 1 ≤ e → Associated (ℓ : O) (ϖ ^ e) →
    ∀ (ε u : PowerSeries O), IsUnit ε → IsUnit u →
    ∀ (b y t : ℕ), 1 ≤ b → (b : ℝ) / (ℓ : ℝ) ≤ (y : ℝ) →
      (Formalism.WindowSums.p1 ℓ ε u) ^ y ∈
        Ideal.span {PowerSeries.C (ϖ ^ t), (PowerSeries.X : PowerSeries O) ^ b} →
      (t : ℝ) / (e : ℝ) ≤ (y : ℝ) - (b : ℝ) / (ℓ : ℝ) + 2 + Real.logb (ℓ : ℝ) (y : ℝ)

def LenPi0 : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (R : Type) [AddCommGroup R]
    [Module O R] [Module.Free O R] [Module.Finite O R] (ℓ : O), ℓ ≠ 0 →
    ∀ q : Module.End O R, IsNilpotent q →
      Module.length O (R ⧸ LinearMap.range (q - ℓ • (1 : Module.End O R))) =
        (Module.finrank O R : ℕ∞) * Module.length O (O ⧸ Ideal.span {ℓ})

def ColChain : Prop :=
  ∀ (O : Type) [CommRing O] (M : Type) [AddCommGroup M] [Module O M] (P : Submodule O M)
    (k : ℕ) (F : ℕ → Submodule O M), F 0 = ⊤ → (∀ i < k, F (i + 1) ≤ F i) →
    Module.length O (M ⧸ P) ≤
      (∑ i ∈ Finset.range k, Module.length O (↥(F i) ⧸ (F (i + 1) ⊔ P).comap (F i).subtype)) +
        Module.length O (↥(F k) ⧸ P.comap (F k).subtype)

def SubGen : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsPrincipalIdealRing O] (M : Type) [AddCommGroup M]
    [Module O M] [Module.Free O M] [Module.Finite O M] (ℓ : O) (e : ℕ) (F P : Submodule O M),
    (∀ x ∈ F, ℓ ^ e • x ∈ P) →
    Module.length O (↥F ⧸ P.comap F.subtype) ≤
      ((Module.finrank O M * e : ℕ) : ℕ∞) * Module.length O (O ⧸ Ideal.span {ℓ})

def ColAssembly : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsPrincipalIdealRing O] (M : Type) [AddCommGroup M]
    [Module O M] [Module.Free O M] [Module.Finite O M] (ℓ : O) (P : Submodule O M) (k : ℕ)
    (F : ℕ → Submodule O M) (gen : Finset ℕ) (m e e' L : ℕ),
    F 0 = ⊤ → (∀ i < k, F (i + 1) ≤ F i) → gen ⊆ Finset.range k →
    (∀ i ∈ gen, (∃ s : Finset M, s.card ≤ m ∧ (↑s : Set M) ⊆ F i ∧
        F i ≤ Submodule.span O (↑s : Set M) ⊔ F (i + 1)) ∧
      ∀ x ∈ F i, ℓ ^ e' • x ∈ F (i + 1) ⊔ P) →
    (∀ i < k, i ∉ gen →
      Module.length O (↥(F i) ⧸ (F (i + 1) ⊔ P).comap (F i).subtype) ≤
        (L : ℕ∞) * Module.length O (O ⧸ Ideal.span {ℓ})) →
    (∀ x ∈ F k, ℓ ^ e • x ∈ P) →
    Module.length O (M ⧸ P) ≤
      ((Module.finrank O M * e + gen.card * m * e' + (k - gen.card) * L : ℕ) : ℕ∞) *
        Module.length O (O ⧸ Ideal.span {ℓ})

end Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains
