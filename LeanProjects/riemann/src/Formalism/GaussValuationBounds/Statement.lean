import Mathlib
import Formalism.WindowSums.Statement
import Formalism.FrobeniusContraction.Statement

noncomputable section

namespace Formalism.NOK

open Polynomial

def sigNOK (ℓ E M j : ℕ) : ℕ :=
  ⌊((E : ℝ) + (M : ℝ) / (ℓ : ℝ) ^ (j - 1)) * (ℓ : ℝ) / ((ℓ : ℝ) - 1) ^ 2⌋₊ + 1

def PowContent : Prop :=
  ∀ (A : Type) [CommRing A] (a X p : A) (N M z c : ℕ), 1 ≤ N →
    p ∈ Ideal.span {a, X ^ N} → c + (M + N - 1) / N ≤ z + 1 →
    p ^ z ∈ Ideal.span {a ^ c, X ^ M}

def SigNum : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime], 3 ≤ ℓ → ∀ (E M j r : ℕ), 1 ≤ j →
    ((ℓ - 1) * r < E → r + padicValNat ℓ r.factorial < sigNOK ℓ E M j) ∧
    (r : ℝ) * ℓ / ((ℓ : ℝ) - 1) -
        max 0 (((ℓ : ℝ) - 1) * r - E - (M : ℝ) / (ℓ : ℝ) ^ (j - 1)) ≤ sigNOK ℓ E M j

def RelCoeff : Prop :=
  ∀ (A : Type) [CommRing A] (ℓ : ℕ) [Fact ℓ.Prime], 3 ≤ ℓ →
    ∀ (X u : A) (p : ℕ → A) (E M j : ℕ), 1 ≤ j →
      p (j - 1) ∈ Ideal.span {(ℓ : A), X ^ (ℓ ^ (j - 1))} →
      ∀ r : ℕ,
        (ℓ : A) ^ sigNOK ℓ E M j * (u * X * ∏ s ∈ Finset.range j, p s ^ (ℓ - 1)) ^ r ∈
          Ideal.span {(ℓ : A) ^ (r + padicValNat ℓ r.factorial),
            X ^ M * ∏ s ∈ Finset.range j, p s ^ E}

def RelVanish : Prop :=
  ∀ (A : Type) [CommRing A] (ℓ : ℕ) (X u : A) (p : ℕ → A) (E M j r : ℕ),
    M ≤ r → E ≤ (ℓ - 1) * r →
    (u * X * ∏ s ∈ Finset.range j, p s ^ (ℓ - 1)) ^ r ∈
      Ideal.span {X ^ M * ∏ s ∈ Finset.range j, p s ^ E}

def Rel1 : Prop :=
  ∀ (A : Type) [CommRing A] (ℓ : ℕ) [Fact ℓ.Prime], 3 ≤ ℓ →
    ∀ (X u : A) (B r : ℕ),
      (ℓ : A) ^ (⌊(B : ℝ) / ((ℓ : ℝ) - 1)⌋₊ + 1) * (u * X * (X + (ℓ : A)) ^ (ℓ - 1)) ^ r ∈
        Ideal.span {(ℓ : A) ^ (r + padicValNat ℓ r.factorial), X * (X + (ℓ : A)) ^ B}

def Rel2 : Prop :=
  ∀ (O : Type) [CommRing O] (ℓ : ℕ) [Fact ℓ.Prime], 3 ≤ ℓ →
    ∀ (ε u' w : PowerSeries O) (b r : ℕ),
      PowerSeries.C ((ℓ : O) ^ (⌊(b : ℝ) / ((ℓ : ℝ) - 1) ^ 2⌋₊ + 1)) *
          (w * (PowerSeries.X - PowerSeries.C (ℓ : O)) * PowerSeries.X ^ (ℓ - 1) *
            (Formalism.WindowSums.p1 ℓ ε u') ^ (ℓ - 1)) ^ r ∈
        Formalism.WindowSums.IdLQ (O := O) ℓ (r + padicValNat ℓ r.factorial) b

def PhiIterX : Prop :=
  ∀ (O A : Type) [CommRing O] [CommRing A] [Algebra O A] (B : Formalism.WachCohomologyFacts.Base O A) (j : ℕ),
    ∃ v : A, IsUnit v ∧
      (⇑B.φ)^[j] B.X = v * B.X * ∏ s ∈ Finset.range j, B.p s ^ (B.ℓ - 1)

def PsIdeal : Prop :=
  ∀ (O A : Type) [CommRing O] [CommRing A] [Algebra O A] (B : Formalism.WachCohomologyFacts.Base O A) (s : ℕ),
    B.p s ∈ Ideal.span {(B.ℓ : A), B.X ^ (B.ℓ ^ s)}

def DelVal : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime], ℓ ≠ 2 → ∀ (χ : ℤ_[ℓ]ˣ), PadicInt.valuation ((χ : ℤ_[ℓ]) - 1) = 1 →
    ∀ r : ℕ,
      (∏ y ∈ Finset.Icc 1 r, (1 - (χ : ℤ_[ℓ]) ^ ((ℓ - 1) * y))) ≠ 0 ∧
      PadicInt.valuation (∏ y ∈ Finset.Icc 1 r, (1 - (χ : ℤ_[ℓ]) ^ ((ℓ - 1) * y))) =
        r + padicValNat ℓ r.factorial

def DSat : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] (ϖ : O), Prime ϖ →
    ∀ (p v : PowerSeries O) (N : ℕ), 1 ≤ N → IsUnit v →
      p - v * PowerSeries.X ^ N ∈ Ideal.span {PowerSeries.C ϖ} →
      ∀ c : O, PowerSeries.C c ∈ Ideal.span {PowerSeries.C ϖ, p} → ϖ ∣ c

def DUDeg : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] (ϖ : O), Prime ϖ →
    ∀ (ℓ : ℕ) (p₀ p₁ v₀ v₁ w : PowerSeries O) (s₀ s₁ b₀ b₁ : ℕ),
      s₀ < s₁ → b₀ < ℓ * b₁ → IsUnit v₀ → IsUnit v₁ → IsUnit w →
      p₀ - v₀ * PowerSeries.X ^ (ℓ ^ s₀) ∈ Ideal.span {PowerSeries.C ϖ} →
      p₁ - v₁ * PowerSeries.X ^ (ℓ ^ s₁) ∈ Ideal.span {PowerSeries.C ϖ} →
      w * p₀ ^ b₀ ∉ Ideal.span {PowerSeries.C ϖ, p₁ ^ b₁}

def LemmaCVal : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (ℓ : ℕ), 2 ≤ ℓ →
    ∀ (E : ℕ → Polynomial O) (u : ℕ → PowerSeries O),
      (∀ s, (E s).IsEisensteinAt (Ideal.span {ϖ})) → (∀ s, (E s).natDegree = ℓ ^ s) →
      (∀ s, IsUnit (u s)) →
      ∀ (ell g a b₀ b₁ s₀ s₁ k : ℕ), s₀ < s₁ →
        2 * ((a : ℝ) + 2 * g * ell) < b₁ → 2 * b₀ ≤ ℓ * b₁ →
        PowerSeries.C (ϖ ^ a) *
            (∏ s ∈ Finset.range ell, (u s * (E s : PowerSeries O)) ^ g) ^ 2 *
            (u s₀ * (E s₀ : PowerSeries O)) ^ b₀ ∈
          Ideal.span {PowerSeries.C (ϖ ^ k), (u s₁ * (E s₁ : PowerSeries O)) ^ b₁} →
        (k : ℝ) ≤ ((a : ℝ) + 2 * g * ell) * b₁ / (b₁ - b₀ / ℓ) ∧
          (k : ℝ) ≤ 2 * ((a : ℝ) + 2 * g * ell)

def ExpNonzero : Prop :=
  ∀ g b : ℤ, 0 ≤ g → g < b →
    ∀ x ∈ Finset.Icc (-g) (-1) ∪ Finset.Icc (-b - g) (-b - 1) ∪ Finset.Icc (b - g) (b - 1), x ≠ 0

def KapBound : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime], ℓ ≠ 2 → ∀ (χ : ℤ_[ℓ]ˣ), PadicInt.valuation ((χ : ℤ_[ℓ]) - 1) = 1 →
    ∀ (ell g h : ℕ) (a : Fin 5 → ℤ) (JJ : Finset ℤ),
      JJ ⊆ Finset.univ.biUnion (fun t => Finset.Ico (a t) (a t + 4 * (g : ℤ))) →
      (∀ i ∈ JJ, |i| ≤ 2 * (h : ℤ)) →
      (Formalism.WindowSums.PP ℓ χ ell JJ).eval 1 ≠ 0 ∧
      (PadicInt.valuation ((Formalism.WindowSums.PP ℓ χ ell JJ).eval 1) : ℝ) ≤
        ell + 20 * g * (1 + ell) + 5 * (4 * g / ((ℓ : ℝ) - 1) + Real.logb ℓ (2 * h))

def WStep (ℓ H lam a : ℝ) : ℝ :=
  max (H / (ℓ - 1)) ((ℓ * a + (ℓ - 1) * (H + lam)) / (ℓ ^ 2 - ℓ + 1)) + 1

def WCycle : Prop :=
  ∀ (n : ℕ) [NeZero n] (ℓ lam Hm : ℝ) (a H : ZMod n → ℝ), 3 ≤ ℓ → 0 ≤ lam →
    (∀ i, H i ≤ Hm) → (∀ i, a (i - 1) ≤ WStep ℓ (H i) lam (a i)) →
    ∀ i, a i ≤ (Hm + lam) / (ℓ - 1) + 2

def WThin : Prop :=
  ∀ (ℓ lam G X₀ : ℝ) (j : ℕ) (x H : ℕ → ℝ), 3 ≤ ℓ → 0 ≤ lam → 0 ≤ G → 0 ≤ X₀ → x 0 ≤ X₀ →
    (∀ k < j, H k ≤ 2 * G) → (∀ k < j, x (k + 1) ≤ WStep ℓ (H k) lam (x k)) →
    x j ≤ X₀ / (ℓ - 1) ^ j + (2 * G + lam) / (ℓ - 1) + 2

def WCut : Prop :=
  ∀ (n : ℕ) [NeZero n] (ℓ lam h G : ℝ) (a H : ZMod n → ℝ) (c : ZMod n) (j : ℕ),
    3 ≤ ℓ → 0 ≤ lam → 0 ≤ h → 0 ≤ G →
    (∀ i, H i ≤ 2 * h) → (∀ k : ℕ, 1 ≤ k → k ≤ j → H (c + k) ≤ 2 * G) →
    (∀ i, a (i - 1) ≤ WStep ℓ (H i) lam (a i)) →
    a c ≤ ((2 * h + lam) / (ℓ - 1) + 2) / (ℓ - 1) ^ j + (2 * G + lam) / (ℓ - 1) + 2

def SigBound : Prop :=
  ∀ (ℓ : ℕ), 3 ≤ ℓ → ∀ (g h j : ℕ), 1 ≤ j →
    (sigNOK ℓ (3 * g) ((h + 2 * g) / (ℓ - 1) + 1) j : ℝ) ≤
      3 / 2 * ((h : ℝ) + 2 * g) / ((ℓ : ℝ) - 1) ^ (j + 1) + 9 / 4 * g + 7 / 4

def ETotal : Prop :=
  ∀ (r sig kap g ell : ℝ), 0 ≤ r → 0 ≤ sig → 0 ≤ g → 0 ≤ ell →
    2 * r + 4 * sig + max r (2 * (2 * sig + r + 2 * g * ell)) + 2 * kap =
      4 * r + 8 * sig + 4 * g * ell + 2 * kap

def CjExist : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime], ℓ ≠ 2 → ∀ (χ : ℤ_[ℓ]ˣ), PadicInt.valuation ((χ : ℤ_[ℓ]) - 1) = 1 →
    ∃ c : ℤ → ℤ_[ℓ], (∀ j, -(ℓ : ℤ_[ℓ]) * c j = ((χ ^ (-j) : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) - 1) ∧ c 0 = 0 ∧
      ∀ j j', j ≠ j' → c j - c j' ≠ 0 ∧ PadicInt.valuation (c j - c j') = padicValInt ℓ (j - j')

def GapPure1 : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (V : Type) [AddCommGroup V] [Module ℤ_[ℓ] V]
    (T : Module.End ℤ_[ℓ] V) (c : ℤ → ℤ_[ℓ]),
    (∀ j j', j ≠ j' → c j - c j' ≠ 0 ∧ PadicInt.valuation (c j - c j') = padicValInt ℓ (j - j')) →
    ∀ (a S η b E : ℕ) (R₁ R₂ : Finset ℤ) (x : V),
      2 * a + S + η ≤ b →
      R₁ ⊆ Finset.Icc ((b : ℤ) - S - a + 1) b →
      R₂ ⊆ Finset.Icc ((b : ℤ) + 1) ((b : ℤ) + S + a) ∪ Finset.Icc (1 - (η : ℤ)) ((η : ℤ) + a) →
      aeval T (∏ j ∈ R₁, (X - C (c j))) x = 0 →
      aeval T (∏ j ∈ R₂, (X - C (c j))) x = 0 →
      ((3 * a + 2 * S + 2 * η : ℕ) : ℝ) / ((ℓ : ℝ) - 1) +
          2 * Real.logb ℓ ((b + S + a + η : ℕ) : ℝ) ≤ E →
      ((ℓ : ℤ_[ℓ]) ^ E) • x = 0

def GapPure2 : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (V : Type) [AddCommGroup V] [Module ℤ_[ℓ] V]
    (T : Module.End ℤ_[ℓ] V) (c : ℤ → ℤ_[ℓ]),
    (∀ j j', j ≠ j' → c j - c j' ≠ 0 ∧ PadicInt.valuation (c j - c j') = padicValInt ℓ (j - j')) →
    ∀ (a S b E : ℕ) (R₁ : Finset ℤ) (x : V),
      a < b →
      R₁ ⊆ Finset.Icc 1 (a : ℤ) ∪ Finset.Icc (-(b : ℤ) - S + 1) (-(b : ℤ) + a) →
      aeval T (X - C (c 0)) x = 0 →
      aeval T (∏ j ∈ R₁, (X - C (c j))) x = 0 →
      ((2 * a + S + 1 : ℕ) : ℝ) / ((ℓ : ℝ) - 1) + 2 * Real.logb ℓ ((b + S + a : ℕ) : ℝ) ≤ E →
      ((ℓ : ℤ_[ℓ]) ^ E) • x = 0

def ExponentSumIdentity : Prop :=
  ∀ (ℓ b b' S E lam : ℝ), 1 < ℓ →
    ((b + S) / (ℓ - 1) + 1) + E + S - b' + (b / (ℓ - 1) ^ 2 + 1) + (b' + S - b / ℓ + 2 + lam) =
      b / (ℓ * (ℓ - 1)) + b / (ℓ - 1) ^ 2 + E + 2 * S + S / (ℓ - 1) + 4 + lam

def SlopeNum : Prop :=
  (∀ ℓ : ℝ, 13 ≤ ℓ → 8 * ℓ / (ℓ - 1) ^ 3 + 2 / (ℓ - 1) ^ 2 < 1 / ℓ) ∧
    (8 * 5 / ((5 : ℝ) - 1) ^ 3 + 2 / ((5 : ℝ) - 1) ^ 2 = 3 / 4)

end Formalism.NOK
