import Mathlib

noncomputable section

namespace Formalism.IrreducibleCountingLemmas.WindowSums

open Polynomial

def QuadRecip : Prop :=
  ∀ (q d : ℕ) [Fact q.Prime] [Fact d.Prime], q % 4 = 3 → d % 4 = 3 → q ≠ d →
    legendreSym q (-(d : ℤ)) = 1 → legendreSym d (-(q : ℤ)) = -1

def OrdNegD : Prop :=
  ∀ (e d : ℕ), 1 ≤ e → d % 16 = 7 → orderOf (-(d : ZMod (2 ^ (e + 2)))) = 2 ^ (e - 1)

def OrdNegQ : Prop :=
  ∀ (e q : ℕ), q % 8 = 3 → orderOf (-(q : ZMod (2 ^ (e + 2)))) = 2 ^ e

def DecompD : Prop :=
  ∀ (H : Type) [AddCommGroup H] (h : H), Even (addOrderOf h) →
    (((1, 1), 0) : (ZMod 2 × ZMod 2) × H) ∉
      AddSubgroup.closure ({((0, 1), 0), ((1, 1), h)} : Set ((ZMod 2 × ZMod 2) × H)) ∧
    ∀ g : (ZMod 2 × ZMod 2) × H, (g + ((0, 1), 0)).1.2 ≠ g.1.2

def DecompDOdd : Prop :=
  ∀ (H : Type) [AddCommGroup H] (h : H), Odd (addOrderOf h) →
    (((1, 1), 0) : (ZMod 2 × ZMod 2) × H) ∈
      AddSubgroup.closure ({((0, 1), 0), ((1, 1), h)} : Set ((ZMod 2 × ZMod 2) × H))

def DecompQ : Prop :=
  ∀ (H : Type) [AddCommGroup H] (h : H) (x : ZMod 2),
    (∀ g ∈ AddSubgroup.closure ({((1, 0), 0), ((x, 0), h)} : Set ((ZMod 2 × ZMod 2) × H)),
      g.1.2 = 0) ∧
    (((1, 1), 0) : (ZMod 2 × ZMod 2) × H) ∉
      AddSubgroup.closure ({((1, 0), 0), ((x, 0), h)} : Set ((ZMod 2 × ZMod 2) × H))

def DecompCard : Prop :=
  ∀ (H : Type) [AddCommGroup H] (h : H), 0 < addOrderOf h →
    (Even (addOrderOf h) →
      Nat.card (AddSubgroup.closure ({((0, 1), 0), ((1, 1), h)} : Set ((ZMod 2 × ZMod 2) × H))) =
        2 * addOrderOf h) ∧
    (∀ x : ZMod 2,
      Nat.card (AddSubgroup.closure ({((1, 0), 0), ((x, 0), h)} : Set ((ZMod 2 × ZMod 2) × H))) =
        2 * addOrderOf h)

def TameOrder : Prop :=
  ∀ l : ℕ, l.Prime → l % 4 = 3 → Odd ((l - 1) / 2) ∧ Nat.Coprime ((l - 1) / 2) l

def KillingNoTwist : Prop :=
  ∀ (l t r : ℕ) (a : ℤ), l % 2 = 1 → 4 * t * r + 1 < l → 1 ≤ r → a ≠ 0 → |a| ≤ 2 * t →
    t * r < (l - 1) / 2 ∧ ¬ ((((l - 1) / 2 : ℕ) : ℤ) ∣ a * r)

def DictVal : Prop :=
  ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ u : ℤ_[l]ˣ, ((u : ℤ_[l]) - 1).valuation = 1 →
    ∀ s : ℕ, ¬ l ∣ s →
    (∀ y : ℕ, 1 ≤ y → ((u : ℤ_[l]) ^ (s * y) - 1).valuation = 1 + padicValNat l y) ∧
    (∀ y y' : ℕ, y' < y →
      ((u : ℤ_[l]) ^ (s * y) - (u : ℤ_[l]) ^ (s * y')).valuation = 1 + padicValNat l (y - y'))

def FiltProd : Prop :=
  ∀ (R V : Type) [CommRing R] [AddCommGroup V] [Module R V] (T : Module.End R V)
    (F : ℕ → Submodule R V) (c : ℕ → R) (k a : ℕ),
    (∀ i, k ≤ i → i < k + a → ∀ x ∈ F i, T x - c i • x ∈ F (i + 1)) →
    ∀ x ∈ F k, aeval T (∏ i ∈ Finset.Ico k (k + a), (X - C (c i))) x ∈ F (k + a)

def TwoPolyKill : Prop :=
  ∀ (R V : Type) [CommRing R] [AddCommGroup V] [Module R V] (T : Module.End R V)
    (W : Submodule R V) (P₁ P₂ : R[X]) (d : R) (y : V),
    (∀ x ∈ W, T x ∈ W) → C d ∈ Ideal.span ({P₁, P₂} : Set R[X]) →
    aeval T P₁ y ∈ W → aeval T P₂ y ∈ W → d • y ∈ W

def RhoW : Prop :=
  ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ u : ℤ_[l]ˣ, ((u : ℤ_[l]) - 1).valuation = 1 →
    ∀ s : ℕ, ¬ l ∣ s →
    ∀ (V : Type) [AddCommGroup V] [Module ℤ_[l] V] (γ : Module.End ℤ_[l] V) (a : ℕ) (x : V),
      aeval γ (∏ i ∈ Finset.range a, (X - C ((u : ℤ_[l]) ^ (s * i)))) x = 0 →
      aeval γ (∏ i ∈ Finset.Ico a (2 * a), (X - C ((u : ℤ_[l]) ^ (s * i)))) x = 0 →
      ((l : ℤ_[l]) ^ (2 * a - 1 + padicValNat l (2 * a - 1).factorial)) • x = 0 ∧
      ((l : ℤ_[l]) ^ (2 * a + padicValNat l (2 * a).factorial)) • x = 0

def CokerW : Prop :=
  ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ u : ℤ_[l]ˣ, ((u : ℤ_[l]) - 1).valuation = 1 →
    ∀ s : ℕ, ¬ l ∣ s →
    ∀ (V : Type) [AddCommGroup V] [Module ℤ_[l] V] (γ ϖ : Module.End ℤ_[l] V)
      (N' : Submodule ℤ_[l] V) (a : ℕ),
      Function.Injective ϖ → (∀ x ∈ N', ϖ x ∈ N') → (∀ x, (ϖ ^ a) x ∈ N') →
      (∀ (i : ℕ) (x : V), ∃ y, γ ((ϖ ^ i) x) - (u : ℤ_[l]) ^ (s * i) • (ϖ ^ i) x = (ϖ ^ (i + 1)) y) →
      (∀ (i : ℕ), ∀ x ∈ N', ∃ y ∈ N',
        γ ((ϖ ^ i) x) - (u : ℤ_[l]) ^ (s * i) • (ϖ ^ i) x = (ϖ ^ (i + 1)) y) →
      ∀ x : V, ((l : ℤ_[l]) ^ (2 * a - 1 + padicValNat l (2 * a - 1).factorial)) • x ∈ N'

def RhoBound : Prop :=
  ∀ (l e h H a : ℕ), l.Prime → l ≠ 2 → H ≤ 2 * h →
    a = ⌈((e * H : ℕ) : ℝ) / ((l : ℝ) - 1)⌉₊ →
    ((2 * a + padicValNat l (2 * a).factorial : ℕ) : ℝ) ≤ 9 * ((e * h : ℕ) : ℝ) / l + 3

def HorizDenomS : Prop :=
  ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ u : ℤ_[l]ˣ, ((u : ℤ_[l]) - 1).valuation = 1 →
    ∀ s : ℕ, ¬ l ∣ s → ∀ y : ℕ,
      (∏ i ∈ Finset.Icc 1 y, (1 - (u : ℤ_[l]) ^ (s * i))).valuation =
        y + padicValNat l y.factorial ∧
      ((y + padicValNat l y.factorial : ℕ) : ℝ) ≤ (y : ℝ) * l / ((l : ℝ) - 1)

def HorizSolve : Prop :=
  ∀ (R V : Type) [CommRing R] [AddCommGroup V] [Module R V] (γ ϖ : Module.End R V) (c : ℕ → R),
    (∀ (i : ℕ) (x : V), ∃ y, γ ((ϖ ^ i) x) - c i • (ϖ ^ i) x = (ϖ ^ (i + 1)) y) →
    ∀ (z' : V) (y : ℕ), ∃ w r : V,
      γ (ϖ w) - ϖ w = (∏ i ∈ Finset.Icc 1 y, (c i - 1)) • ϖ z' + (ϖ ^ (y + 1)) r

def JJFacts : Prop :=
  ∀ (A : Type) [CommRing A] (p E : A) (s M h y : ℕ), 4 * h ≤ s * M → 1 ≤ M → M ≤ y →
    (p ^ M * E ^ (4 * h)) ∣ p ^ y * E ^ (s * y) ∧ (p * (E ^ h) ^ 2) ∣ p ^ M * E ^ (4 * h)

def SigBound : Prop :=
  ∀ (l e s h M σ : ℕ), l.Prime → l ≠ 2 → e * s = l - 1 →
    M = max 1 ⌈(4 * h : ℝ) / s⌉₊ → σ = ⌈(M : ℝ) * l / ((l : ℝ) - 1)⌉₊ →
    4 * h ≤ s * M ∧ (M : ℝ) ≤ 6 * ((e * h : ℕ) : ℝ) / l + 1 ∧
      (σ : ℝ) ≤ 9 * ((e * h : ℕ) : ℝ) / l + 3

def ContractBij : Prop :=
  ∀ (R P : Type) [CommRing R] [AddCommGroup P] [Module R P] (I : Ideal R) [IsAdicComplete I P]
    (f : P →+ P),
    (∀ k : ℕ, ∀ x ∈ (I ^ k • ⊤ : Submodule R P), f x ∈ (I ^ (k + 1) • ⊤ : Submodule R P)) →
    Function.Bijective (fun x => f x - x)

def KappaBound : Prop :=
  ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ u : ℤ_[l]ˣ, ((u : ℤ_[l]) - 1).valuation = 1 →
    ∀ (e S h : ℕ) (b : Fin e → ℕ) (up : Fin e → Bool), (∀ τ, 1 ≤ b τ ∧ b τ ≤ h) →
      ((∏ i ∈ Finset.univ.biUnion (fun τ : Fin e =>
            if up τ then Finset.Ico (-(b τ : ℤ) - S) (-(b τ : ℤ))
            else Finset.Ico (b τ : ℤ) ((b τ : ℤ) + S)),
          (1 - ((u ^ i : ℤ_[l]ˣ) : ℤ_[l]))).valuation : ℝ) ≤
        (e : ℝ) * ((S : ℝ) + (S : ℝ) / ((l : ℝ) - 1) + Real.logb l ((h : ℝ) + S))

def EvalOneMod : Prop :=
  ∀ (R V : Type) [CommRing R] [AddCommGroup V] [Module R V] (T : Module.End R V)
    (W : Submodule R V) (w : V), (∀ x ∈ W, T x ∈ W) → T w - w ∈ W →
    ∀ P : R[X], aeval T P w - P.eval 1 • w ∈ W

def MixedA : Prop :=
  ∀ (O K : Type) [CommRing O] [IsDomain O] [Field K] [Algebra O K] [IsFractionRing O K]
    (δ : O) (x : K) (bU B : ℕ), bU < B →
    (∀ i < B, ∃ c : O, algebraMap O K c = x * algebraMap O K (((X + C δ) ^ bU : O[X]).coeff i)) →
    ∃ c : O, algebraMap O K c = x

def MixedC : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (O K : Type) [CommRing O] [IsDomain O] [Algebra ℤ_[l] O] [Field K]
    [Algebra O K] [IsFractionRing O K] (δ ε : O) (x : K) (bU B : ℕ),
    IsUnit ε → δ ^ 2 = (l : O) * ε → 1 ≤ B → B ≤ bU →
    (∀ i < B, ∃ c : O, algebraMap O K c = x * algebraMap O K (((X + C δ) ^ bU : O[X]).coeff i)) →
    ∃ c : O, algebraMap O K c = (l : K) ^ ((bU - B + 2) / 2 + Nat.log l bU) * x

def MixedCNum : Prop :=
  ∀ (l bU B η h : ℕ), l.Prime → B ≤ bU → bU ≤ B + 2 * η → bU ≤ h →
    (bU - B + 2) / 2 + Nat.log l bU ≤ η + 1 + Nat.log l h ∧
    ∀ k, k ≤ bU → padicValNat l (bU.choose k) ≤ Nat.log l bU

def ColengthTwoStep : Prop :=
  ∀ (O M : Type) [CommRing O] [AddCommGroup M] [Module O M] (l g g₀ e e' : ℕ)
    (Z Bc I : Submodule O M) (s s₀ : Finset M),
    s.card ≤ g → Submodule.span O (s : Set M) ⊔ Bc = Z → Bc ≤ I →
    s₀.card ≤ g₀ → (s₀ : Set M) ⊆ Z →
    (∀ p ∈ Z, (l ^ e : ℕ) • p ∈ Submodule.span O (s₀ : Set M) ⊔ I) →
    (∀ p ∈ Submodule.span O (s₀ : Set M), (l ^ e' : ℕ) • p ∈ I) →
    Module.length O (↥Z ⧸ I.comap Z.subtype) ≤
      ((g : ℕ∞) * (e : ℕ∞) + (g₀ : ℕ∞) * (e' : ℕ∞)) * Module.length O (O ⧸ Ideal.span {(l : O)})

def CostB : Prop :=
  ∀ (r b l S t η L m : ℝ), 0 ≤ r → 0 ≤ b → 0 < l → 0 ≤ L → 0 ≤ m → r ≤ m * l →
    r * (S + t + η) ≤ m * b →
    r * (b / l + S + t + η + L) + m * b ≤ 3 * (m * b) + r * L ∧
    (L ≤ S + t + η → r * (b / l + S + t + η + L) + m * b ≤ 4 * (m * b))

def CountB : Prop :=
  ∀ (ι : Type) [Fintype ι] (n : ι → ℕ) (f : ℕ), (∀ w, 1 ≤ n w) → ∑ w, 2 * n w = 2 * f →
    ∑ w, (n w * 2 + 1) ≤ 3 * f ∧ ∑ w, n w * 2 * (2 + 1) = 6 * f

def StableGraded : Prop :=
  ∀ (F V ι : Type) [Field F] [AddCommGroup V] [Module F V] (θ : Module.End F V)
    (W : Submodule F V), (∀ x ∈ W, θ x ∈ W) →
    ∀ (J : Finset ι) (c : ι → F), Set.InjOn c J → ∀ x : ι → V, (∀ j ∈ J, θ (x j) = c j • x j) →
      ∑ j ∈ J, x j ∈ W → ∀ j ∈ J, x j ∈ W

def SatPow : Prop :=
  ∀ (A : Type) [CommRing A] (E l : A), (∀ x y : A, E * x = E * y → x = y) →
    (∀ x y : A, l * x = E * y → ∃ z, x = E * z) →
    ∀ (j : ℕ) (x y : A), l * x = E ^ j * y → ∃ z, x = E ^ j * z

def NormFrob : Prop :=
  ∀ (x : ℝ) (l : ℕ), 0 ≤ x → 2 ≤ l → x ^ l ≤ max x 1 → x ≤ 1

def FactorialValuationRealBounds : Prop :=
  ∀ (l : ℕ), l.Prime →
    (∀ j : ℕ, 1 ≤ j → (padicValNat l j.factorial : ℝ) ≤ ((j : ℝ) - 1) / ((l : ℝ) - 1) ∧
      ((j : ℝ) - 1) / ((l : ℝ) - 1) ≤ 2 * j / l) ∧
    (∑' j : ℕ, (2 / (l : ℝ)) / (l : ℝ) ^ j = 2 / ((l : ℝ) - 1)) ∧
    (∀ H : ℕ, 8 * H + 1 ≤ l → 2 * (4 * (H : ℝ)) / ((l : ℝ) - 1) ≤ 1)

def OrbitRatio : Prop :=
  ∀ (G : Type) [CommGroup G] (F : G →* G) (Sig : Finset G) (N : ℕ), Function.Injective F →
    (1 : G) ∈ Sig → (∀ x ∈ Sig, F x ∈ Sig) → Sig.card ≤ N → 2 ≤ N →
    ∀ a ∈ Sig, ∀ a' ∈ Sig,
      0 < Function.minimalPeriod F (a / a') ∧ 4 * Function.minimalPeriod F (a / a') ≤ N ^ 2

def DigitPeriodLower : Prop :=
  ∀ (l a c ρ : ℕ), 2 ≤ l → 0 < c → 1 ≤ ρ → (l ^ a - 1) ∣ c * (l ^ ρ - 1) →
    l ^ a - 1 ≤ c * (l ^ ρ - 1)

def DigitLemma : Prop :=
  ∀ (l a c ρ : ℕ) (m : ℤ), l.Prime → 1 ≤ a → 0 < c → c < l ^ a - 1 → 1 ≤ ρ →
    (l ^ a - 1) ∣ c * (l ^ ρ - 1) → |m| < l →
    padicValInt l ((c : ℤ) + m * ((l : ℤ) ^ a - 1)) ≤ ρ

def LagrangeBoundT : Prop :=
  ∀ (l a A' r' : ℕ) (Cc : Finset ℕ), l.Prime → 1 ≤ a → 2 * A' < l →
    (∀ c ∈ Cc, c < l ^ a - 1) →
    (∀ c ∈ Cc, ∀ c' ∈ Cc, c ≠ c' → ∃ ρ, 1 ≤ ρ ∧ ρ ≤ r' ∧
      ((l : ℤ) ^ a - 1) ∣ ((c : ℤ) - c') * ((l : ℤ) ^ ρ - 1)) →
    ∀ c ∈ Cc, ∀ n < A',
      (∑ c' ∈ Cc, ∑ n' ∈ Finset.range (2 * A'),
        if c' = c ∧ n' = n then 0
        else padicValInt l (((c : ℤ) + n * ((l : ℤ) ^ a - 1)) - ((c' : ℤ) + n' * ((l : ℤ) ^ a - 1))))
      ≤ (Cc.card - 1) * r'

def LagrangeT : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (D₁ D₂ : Finset ℤ) (ρ : ℕ), Disjoint D₁ D₂ →
    (∀ i ∈ D₁, (∑ j ∈ D₂, padicValInt l (i - j)) + ∑ j ∈ D₁.erase i, padicValInt l (i - j) ≤ ρ) →
    C ((l : ℤ_[l]) ^ ρ) ∈ Ideal.span ({∏ i ∈ D₁, (X - C ((i : ℤ) : ℤ_[l])),
      ∏ j ∈ D₂, (X - C ((j : ℤ) : ℤ_[l]))} : Set ℤ_[l][X])

def BinomIdeal : Prop :=
  ∀ (A : Type) [CommRing A] (E p : A) (h b η : ℕ), 1 ≤ b →
    (E - p) ^ (h + b - 1) ∈ Ideal.span ({E ^ h, p ^ b} : Set A) ∧
    ∃ c, (E - p) ^ η = E ^ η + p * c

def frob {O : Type} [CommRing O] (l : ℕ) (f : PowerSeries O) : PowerSeries O :=
  PowerSeries.mk fun n => if l ∣ n then PowerSeries.coeff (n / l) f else 0

def FrobSpec : Prop :=
  ∀ (O : Type) [CommRing O] (l : ℕ), 1 ≤ l →
    frob l (PowerSeries.X : PowerSeries O) = PowerSeries.X ^ l ∧
    (∀ a : O, frob l (PowerSeries.C a) = PowerSeries.C a) ∧
    (∀ f g : PowerSeries O, frob l (f + g) = frob l f + frob l g) ∧
    (∀ f g : PowerSeries O, frob l (f * g) = frob l f * frob l g)

def FrobDescent : Prop :=
  ∀ (O : Type) [CommRing O] (l : ℕ), 1 ≤ l → ∀ (bb : Ideal (PowerSeries O)) (j : ℕ)
    (x : PowerSeries O), j < l →
    PowerSeries.X ^ j * frob l x ∈ Ideal.span (frob l '' (bb : Set (PowerSeries O))) → x ∈ bb

def SBound : Prop :=
  ∀ (l s e h b : ℕ), 2 ≤ l → 1 ≤ b → h + b ≤ l → l * s ≤ s + e * (h + b - 1) →
    l * s ≤ e * (h + b)

def PowerAbsorb : Prop :=
  ∀ (A Q : Type) [CommRing A] [AddCommGroup Q] [Module A Q] (p : A) (ρ b : ℕ), ρ < b →
    (∃ k : ℕ, ∀ q : Q, p ^ k • q = 0) → (∀ q : Q, ∃ q' : Q, p ^ ρ • q = p ^ b • q') →
    ∀ q : Q, p ^ ρ • q = 0

def RZero : Prop :=
  ∀ (R : Type) [CommRing R] (P : R[X]), ∃ P₁ : R[X], P = C (P.eval 0) + X * P₁ ∧
    ∀ (V : Type) [AddCommGroup V] [Module R V] (T : Module.End R V) (w : V),
      aeval T P w = 0 → P.eval 0 • w = - T (aeval T P₁ w)

def ELVal : Prop :=
  ∀ (l a : ℕ), l.Prime → 1 ≤ a → ∀ (U : Finset ℤ) (η : ℕ) (J : Finset ℤ),
    (∀ n ∈ J, n ≠ 0 ∧ |n| < l ∧ ∃ i ∈ U, ∃ k ∈ Finset.Icc (1 : ℤ) η, n = i + k) →
    padicValInt l (∏ n ∈ J, (0 - n * ((l : ℤ) ^ a - 1) * l)) = J.card ∧ J.card ≤ U.card * η

def NumT : Prop :=
  ∀ (l H η N r' : ℕ), 2 ≤ N → 1 ≤ η → η < H → 4 * r' ≤ N ^ 2 → 40 * (H * N ^ 2 + N ^ 3) < l →
    2 * (H + η + (2 * N * r' + 1)) + 2 < l ∧ 10 * H + 2 ≤ l ∧ 14 * H + (N + 2) * η < l ∧
      8 * H + 1 ≤ l ∧ H + η < l ∧ 4 * η * r' + 4 < l

def CountT : Prop :=
  ∀ (N r' η : ℕ), 2 ≤ N → 1 ≤ r' → 1 ≤ η → 4 * r' ≤ N ^ 2 →
    2 * (2 * N * r') + 2 * η + (N + 1) * η + (η * (r' + 1) + 2 * N * r') + η * (r' + 1) + 1 =
      6 * N * r' + η * (N + 2 * r' + 5) + 1 ∧
    6 * N * r' + η * (N + 2 * r' + 5) + 1 ≤ 7 * (N * r' + η * (N + r')) ∧
    N * r' + η * (N + r') ≤ N ^ 2 * (N + η)

def LiftExp : Prop :=
  ∀ (l h : ℕ) (J : Finset ℤ), l.Prime → l ≠ 2 → J ⊆ Finset.Icc (-(h : ℤ)) (2 * h) → (0 : ℤ) ∉ J →
    2 * (2 * (2 * h) + padicValNat l (2 * (2 * h)).factorial) +
      ((∑ j ∈ J, (1 + padicValInt l j)) + h + padicValNat l h.factorial) ≤ 18 * h

def TailExpII : Prop :=
  ∀ (l H η n : ℕ), l.Prime → 1 ≤ η → η < H → H + η < l → 1 ≤ n →
    padicValNat l (l ^ n).factorial = ∑ i ∈ Finset.range n, l ^ i ∧
    -(3 * (H : ℤ)) ≤ ((∑ i ∈ Finset.range n, l ^ i : ℕ) : ℤ) + n - (H + η + 1) - n * η ∧
    (2 ≤ n →
      (l : ℤ) - 14 * H ≤ ((∑ i ∈ Finset.range n, l ^ i : ℕ) : ℤ) + n - (H + η + 1) - n * η)

def TailExpIII : Prop :=
  ∀ (l η r' n : ℕ), 1 ≤ η → 1 ≤ r' → 4 * η * r' + 4 < l → 1 ≤ n →
    -((η : ℤ) * (r' + 1)) ≤ ((∑ i ∈ Finset.range (n - r'), l ^ i : ℕ) : ℤ) + n - n * η

def KernelMod : Prop :=
  ∀ (A M₁ M₂ : Type) [CommRing A] [AddCommGroup M₁] [Module A M₁] [AddCommGroup M₂] [Module A M₂]
    (f : M₁ →ₗ[A] M₂) (a c : A), (∀ m₂ : M₂, ∃ m₁ : M₁, f m₁ = c • m₂) →
    ∀ (m₁ : M₁) (m₂ : M₂), f m₁ = a • m₂ → ∃ m₀ m₁' : M₁, f m₀ = 0 ∧ c • m₁ = m₀ + a • m₁'

def SuccApprox : Prop :=
  ∀ (R Y Z : Type) [CommRing R] [AddCommGroup Y] [Module R Y] [AddCommGroup Z] [Module R Z] (p : R)
    [IsAdicComplete (Ideal.span {p}) Y] [IsHausdorff (Ideal.span {p}) Z]
    (Lc P : Y →ₗ[R] Z) (I : Submodule R Z) (c k : ℕ), c < k →
    (∀ z : Z, p • z ∈ I → z ∈ I) → (∀ y, Lc y ∈ I) → (∀ y, Lc y + p ^ k • P y ∈ I) →
    (∀ z ∈ I, ∃ y, Lc y = p ^ c • z) →
    ∀ om ∈ I, ∃ y₀, Lc y₀ + p ^ k • P y₀ = p ^ c • om

def GLCardVal : Prop :=
  ∀ (g g' r : ℕ) [Fact g.Prime] [Fact g'.Prime], g ≠ g' →
    padicValNat g (Nat.card (Matrix.GeneralLinearGroup (Fin r) (ZMod g))) = r * (r - 1) / 2 ∧
    padicValNat g (Nat.card (Matrix.GeneralLinearGroup (Fin r) (ZMod g'))) =
      ∑ a ∈ Finset.Icc 1 r, padicValNat g (g' ^ a - 1)

def CentralIdemIntegral : Prop :=
  ∀ (G K : Type) [Group G] [Finite G] [Field K] [CharZero K] (e : MonoidAlgebra K G),
    e * e = e → (∀ y : MonoidAlgebra K G, e * y = y * e) →
    ∀ x : G, IsIntegral ℤ ((Nat.card G : K) * e.coeff x)

def CutVal : Prop :=
  ∀ (g g' Y r f : ℕ), 2 ≤ Y → Y ≤ g → g' ≤ 2 * Y →
    (∀ a ∈ Finset.Icc 1 r,
      ((g : ℝ) ^ (padicValNat g (g' ^ a - 1))) ≤ (g' : ℝ) ^ ((a : ℝ) / 4)) →
    ((∑ a ∈ Finset.Icc 1 r, padicValNat g (g' ^ a - 1) : ℕ) : ℝ) ≤ (r : ℝ) * (r + 1) / 4 ∧
    (f : ℝ) * (r * (r - 1) / 2) + f * (r * (r + 1) / 4) ≤ 2 * f * (r : ℝ) ^ 2

def QuadraticCountBound : Prop :=
  ∀ (f r t η e' : ℕ), 1 ≤ r →
    f * (2 * ((2 * r + t * 2) * e')) = 4 * f * (r + t) * e' ∧
    (r + t) ^ 2 * ((r + t) + (η + t + 1)) ≤ 2 * ((r + t) ^ 2 * ((r + t) + η + t))

end Formalism.IrreducibleCountingLemmas.WindowSums
