import Mathlib
import Formalism.WindowSums.Statement
import Formalism.GaussValuationBounds.Statement

noncomputable section

namespace Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingBounds

open PowerSeries

def PowMemIdealPowXPowOfMemSpan : Prop :=
  ∀ (O : Type) [CommRing O] (ℓ : ℕ) [Fact ℓ.Prime] (p₂ : PowerSeries O) (y B c : ℕ),
    p₂ ∈ Ideal.span {PowerSeries.C (ℓ : O), (PowerSeries.X : PowerSeries O) ^ (ℓ ^ 2)} →
    (c : ℝ) ≤ (y : ℝ) + 1 - (B : ℝ) / (ℓ : ℝ) ^ 2 →
    p₂ ^ y ∈ Formalism.WindowSums.IdLQ (O := O) ℓ c B

def PowMemSpanOfMemSpanLinearDistinguished : Prop :=
  ∀ (O : Type) [CommRing O] (ℓ : ℕ) [Fact ℓ.Prime] (ε u p₂ : PowerSeries O) (w B η c : ℕ),
    p₂ ∈ Ideal.span {PowerSeries.C (ℓ : O), (Formalism.WindowSums.p1 ℓ ε u) ^ ℓ} →
    (c : ℝ) ≤ (w : ℝ) - (B : ℝ) / (ℓ : ℝ) - (η : ℝ) / (ℓ : ℝ) ^ 2 →
    p₂ ^ w ∈ Ideal.span {PowerSeries.C ((ℓ : O) ^ c),
      (Formalism.WindowSums.p1 ℓ ε u) ^ B * (PowerSeries.X : PowerSeries O) ^ η}

def BinomSplit : Prop :=
  ∀ (R : Type) [CommRing R] (x y : R) (a s : ℕ), 1 ≤ a + s →
    (x + y) ^ (a + s - 1) ∈ Ideal.span {x ^ a, y ^ s}

def LemmaGLag : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (V : Type) [AddCommGroup V] [Module ℤ_[ℓ] V]
    (T : Module.End ℤ_[ℓ] V) (c : ℤ → ℤ_[ℓ]),
    (∀ j j', j ≠ j' → c j - c j' ≠ 0 ∧ PadicInt.valuation (c j - c j') = padicValInt ℓ (j - j')) →
    ∀ (a S η b E : ℕ) (R₂ : Finset ℤ) (x : V),
      2 * a + η + 1 ≤ b →
      R₂ ⊆ Finset.Icc ((b : ℤ) + 1) ((b : ℤ) + S + a) ∪ Finset.Icc (1 - (η : ℤ)) ((η : ℤ) + a) →
      Polynomial.aeval T (∏ i ∈ Finset.range a,
        (Polynomial.X - Polynomial.C (c ((b : ℤ) - (i : ℤ))))) x = 0 →
      Polynomial.aeval T (∏ j ∈ R₂, (Polynomial.X - Polynomial.C (c j))) x = 0 →
      ((3 * a + S + 2 * η : ℕ) : ℝ) / ((ℓ : ℝ) - 1) +
          2 * Real.logb ℓ ((b + S + a + η : ℕ) : ℝ) ≤ E →
      ((ℓ : ℤ_[ℓ]) ^ E) • x = 0

def KapWin : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime], ℓ ≠ 2 → ∀ (χ : ℤ_[ℓ]ˣ), PadicInt.valuation ((χ : ℤ_[ℓ]) - 1) = 1 →
    ∀ (ell K D : ℕ) (a : Fin K → ℤ) (L : Fin K → ℕ) (JJ : Finset ℤ),
      JJ ⊆ Finset.univ.biUnion (fun k => Finset.Ico (a k) (a k + (L k : ℤ))) →
      (∀ i ∈ JJ, |i| ≤ (D : ℤ)) →
      (Formalism.WindowSums.PP ℓ χ ell JJ).eval 1 ≠ 0 ∧
      (PadicInt.valuation ((Formalism.WindowSums.PP ℓ χ ell JJ).eval 1) : ℝ) ≤
        (ell : ℝ) + ((∑ k, L k : ℕ) : ℝ) * (1 + ell) +
          ∑ k, ((L k : ℝ) / ((ℓ : ℝ) - 1) + Real.logb ℓ D)

def ColTwoStep : Prop :=
  ∀ (O M : Type) [CommRing O] [AddCommGroup M] [Module O M] (ℓ g g₀ e e' : ℕ)
    (Z I : Submodule O M) (s s₀ : Finset M),
    I ≤ Z → s.card ≤ g → s₀.card ≤ g₀ → (↑s₀ : Set M) ⊆ Z →
    Submodule.span O (s : Set M) ⊔ I = Z →
    (∀ p ∈ Z, (ℓ ^ e : ℕ) • p ∈ Submodule.span O (s₀ : Set M) ⊔ I) →
    (∀ p ∈ Submodule.span O (s₀ : Set M), (ℓ ^ e' : ℕ) • p ∈ I) →
    Module.length O (↥Z ⧸ I.comap Z.subtype) ≤
      ((g * e + g₀ * e' : ℕ) : ℕ∞) * Module.length O (O ⧸ Ideal.span {(ℓ : O)})

def sigT (ℓ E M j : ℕ) : ℕ :=
  ⌈((E : ℝ) + (M : ℝ) / (ℓ : ℝ) ^ (j - 1)) * (ℓ : ℝ) / ((ℓ : ℝ) - 1) ^ 2⌉₊ + 1

def SigA : Prop :=
  ∀ (ℓ : ℕ), 11 ≤ ℓ → ∀ (G h j : ℕ), 1 ≤ j →
    (2 * sigT ℓ (2 * G) (2 * h / (ℓ - 1) + 1) j : ℝ) ≤ 0.05 * h + 0.5 * G + 5

def SigB : Prop :=
  ∀ (ℓ : ℕ), 11 ≤ ℓ → ∀ (w S h : ℕ),
    (sigT ℓ (2 * (w + S)) (2 * h / (ℓ - 1) + 1) 1 : ℝ) ≤
      3 * ((w : ℝ) + S) / ℓ + 3 * (h : ℝ) / (ℓ : ℝ) ^ 2 + 3

def CorAWordUD : Prop :=
  ∀ (ℓ j j' w S η b bU A : ℕ), 11 ≤ ℓ → 1 ≤ j → j' ≤ 3 * j + 1 →
    10 * (j + 1) * (w + S + η + 1) ≤ b → b ≤ bU →
    (A : ℝ) ≤ (((b + η + S : ℕ) : ℝ) + (η : ℝ)) / ((ℓ : ℝ) - 1) + 1 →
    A + η + 2 * sigT ℓ (2 * (w + S + η)) (2 * (b + η + S) / (ℓ - 1) + 1) j +
      2 * j' * (w + S + η) + 1 ≤ bU

def CorAWordDU : Prop :=
  ∀ (ℓ s g b bU bD η S : ℕ), 2 ≤ ℓ → s < g → bU ≤ b + η → η < b → b ≤ bD →
    bU * ℓ ^ s < (bD + S) * ℓ ^ g

def Clusters {n : ℕ} (j : ℕ) (thick : ZMod n → Prop) : Prop :=
  ∀ t, thick t →
    (∀ k : ℕ, 1 ≤ k → k ≤ j → ¬ thick (t - k)) ∨
    (∃ d : ℕ, 1 ≤ d ∧ d ≤ j ∧ thick (t - d) ∧ ∀ k : ℕ, 1 ≤ k → k ≤ d + j → k ≠ d → ¬ thick (t - k))

def CutsExist : Prop :=
  ∀ (n j : ℕ) [NeZero n] (thick : ZMod n → Prop) [DecidablePred thick],
    1 ≤ j → j + 1 ≤ n → Clusters j thick →
    ∃ (m : ℕ) (c : ℕ → ℤ), 1 ≤ m ∧ c m = c 0 + n ∧
      ∀ k < m,
        (∀ i : ℕ, 1 ≤ i → i ≤ j → ¬ thick ((c k + i : ℤ) : ZMod n)) ∧
        (j : ℤ) ≤ c (k + 1) - c k ∧ c (k + 1) - c k ≤ 3 * j + 1 ∧
        ((Finset.Ioc (c k) (c (k + 1))).filter (fun i : ℤ => thick (i : ZMod n))).card ≤ 2

end Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingBounds
