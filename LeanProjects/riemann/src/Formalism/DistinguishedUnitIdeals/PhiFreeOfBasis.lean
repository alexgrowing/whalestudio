import Mathlib
import Formalism.DistinguishedUnitIdeals.FrobeniusDiffBijective
import Formalism.DistinguishedUnitIdeals.ExistsConstOfInvariantMod

noncomputable section

namespace Formalism.ExponentWindows.E

open PowerSeries

def FactVval {O : Type} [CommRing O] (u : Oˣ) (ℓ : ℕ) : Prop :=
  ∀ m : ℤ, m ≠ 0 → ∃ ε : Oˣ, 1 - ((u ^ m : Oˣ) : O) = (ε : O) * (ℓ : O) ^ (1 + padicValInt ℓ m)

def FactVvalOf : Prop :=
  ∀ (O : Type) [CommRing O] [IsLocalRing O] (ℓ : ℕ) (u x : Oˣ), ℓ.Prime → 3 ≤ ℓ →
    ¬ IsUnit (ℓ : O) → (u : O) = 1 + (ℓ : O) * (x : O) → FactVval u ℓ

def FactVOf : Prop :=
  ∀ (O LL Ks Δ : Type) [CommRing O] [Field LL] [Algebra O LL] [CommRing Ks] [Algebra LL Ks]
    (Lev : G.Level LL Ks Δ) (u : Oˣ) (ℓ : ℕ), (Lev.u : LL) = algebraMap O LL (u : O) →
    (ℓ : LL) ≠ 0 → FactVval u ℓ → Lev.FactV

def kapExp (ℓ E : ℕ) (JS : Finset ℤ) : ℕ :=
  E + ∑ i ∈ JS.erase 0, (1 + E + padicValInt ℓ i)

def PPevalVal : Prop :=
  ∀ (O : Type) [CommRing O] (u : Oˣ) (ℓ E : ℕ) (JS : Finset ℤ), ℓ.Prime → FactVval u ℓ →
    ∃ ε : Oˣ, (G.PPoly u ℓ E JS).eval 1 = (ε : O) * (ℓ : O) ^ kapExp ℓ E JS

def PPvalOf : Prop :=
  ∀ (O : Type) [CommRing O] (u : Oˣ) (ℓ E kap : ℕ) (JS JS' : Finset ℤ), ℓ.Prime → FactVval u ℓ →
    2 * E + ∑ i ∈ JS.erase 0, (1 + E + padicValInt ℓ i) +
      ∑ i ∈ JS'.erase 0, (1 + E + padicValInt ℓ i) ≤ 2 * kap →
    PPval ℓ kap (G.PPoly u ℓ E JS) (G.PPoly u ℓ E JS')

def InWindows (JS : Finset ℤ) (K : ℕ) (a : Fin K → ℤ) (y : Fin K → ℕ) (R : ℕ) : Prop :=
  JS ⊆ Finset.univ.biUnion (fun m => Finset.Ico (a m) (a m + (y m : ℤ))) ∧
    ∀ i ∈ JS, |i| ≤ (R : ℤ)

def WinSum : Prop :=
  ∀ (ℓ : ℕ) (JS : Finset ℤ) (K : ℕ) (a : Fin K → ℤ) (y : Fin K → ℕ) (R : ℕ), ℓ.Prime →
    InWindows JS K a y R →
    ((∑ i ∈ JS.erase 0, padicValInt ℓ i : ℕ) : ℝ) ≤
      (∑ m, (y m : ℝ)) / ((ℓ : ℝ) - 1) + (K : ℝ) * Real.logb ℓ R

def kapWin (ℓ E K : ℕ) (y : Fin K → ℕ) (R : ℕ) : ℝ :=
  (E : ℝ) + ((E : ℝ) + 1 + 1 / ((ℓ : ℝ) - 1)) * (∑ m, (y m : ℝ)) + (K : ℝ) * Real.logb ℓ R

def KapExpWin : Prop :=
  ∀ (ℓ E : ℕ) (JS : Finset ℤ) (K : ℕ) (a : Fin K → ℤ) (y : Fin K → ℕ) (R : ℕ), ℓ.Prime →
    InWindows JS K a y R → (kapExp ℓ E JS : ℝ) ≤ kapWin ℓ E K y R

def PPvalWin : Prop :=
  ∀ (O : Type) [CommRing O] (u : Oˣ) (ℓ E kap : ℕ) (JS JS' : Finset ℤ), ℓ.Prime → FactVval u ℓ →
    ∀ (K K' : ℕ) (a : Fin K → ℤ) (y : Fin K → ℕ) (a' : Fin K' → ℤ) (y' : Fin K' → ℕ) (R R' : ℕ),
      InWindows JS K a y R → InWindows JS' K' a' y' R' →
      kapWin ℓ E K y R ≤ (kap : ℝ) → kapWin ℓ E K' y' R' ≤ (kap : ℝ) →
      PPval ℓ kap (G.PPoly u ℓ E JS) (G.PPoly u ℓ E JS')

def PPvalKap : Prop :=
  ∀ (O : Type) [CommRing O] (u : Oˣ) (ℓ E kap g h : ℕ) (JS JS' : Finset ℤ), ℓ.Prime →
    FactVval u ℓ →
    ∀ (a : Fin 3 → ℤ) (y : Fin 3 → ℕ) (a' : Fin 3 → ℤ) (y' : Fin 3 → ℕ),
      InWindows JS 3 a y (2 * h) → InWindows JS' 3 a' y' (2 * h) →
      ∑ m, y m ≤ 7 * g → ∑ m, y' m ≤ 7 * g →
      (E : ℝ) + 7 * (g : ℝ) * ((E : ℝ) + 1 + 1 / ((ℓ : ℝ) - 1)) +
        3 * Real.logb ℓ (2 * (h : ℝ)) ≤ (kap : ℝ) →
      PPval ℓ kap (G.PPoly u ℓ E JS) (G.PPoly u ℓ E JS')

def Base.PhiFree {O : Type} [CommRing O] (B : Base O) (k : ℕ) : Prop :=
  ∃ (r : ℕ) (b : Fin r → PowerSeries O),
    (∀ a : PowerSeries O, ∃ a' : Fin r → PowerSeries O, a = ∑ t, b t * (⇑B.φ)^[k] (a' t)) ∧
    ∀ a' : Fin r → PowerSeries O, ∑ t, b t * (⇑B.φ)^[k] (a' t) = 0 → ∀ t, a' t = 0

def Base.PhiBasis {O : Type} [CommRing O] (B : Base O) (k : ℕ) : Prop :=
  (∀ a : PowerSeries O, ∃ a' : Fin (B.ℓ ^ k) → PowerSeries O,
    a = ∑ t : Fin (B.ℓ ^ k), X ^ (t : ℕ) * (⇑B.φ)^[k] (a' t)) ∧
  ∀ a' : Fin (B.ℓ ^ k) → PowerSeries O,
    ∑ t : Fin (B.ℓ ^ k), X ^ (t : ℕ) * (⇑B.φ)^[k] (a' t) = 0 → ∀ t, a' t = 0

def IsUnitObj {O : Type} [CommRing O] {B : Base O} {n : ℕ} {V₀ : Type} [AddCommGroup V₀]
    [Module (PowerSeries O) V₀] (L₀ : Lat B n V₀) (e₀ : V₀) : Prop :=
  (∀ i, L₀.N i = Submodule.span (PowerSeries O) {e₀}) ∧ (∀ i, L₀.φ i e₀ = e₀) ∧
    ∀ a : PowerSeries O, a • e₀ = 0 → a = 0

def PhiFreeOfBasis : Prop :=
  ∀ (O : Type) [CommRing O] (B : Base O) (k : ℕ), B.PhiBasis k → B.PhiFree k

def PhiFreeOf : Prop :=
  ∀ (O : Type) [CommRing O] (B : Base O) (n : ℕ) (V₀ : Type) [AddCommGroup V₀]
    [Module (PowerSeries O) V₀] (L₀ : Lat B n V₀) (e₀ : V₀) (i : ZMod n) (k : ℕ),
    B.PhiFree k → IsUnitObj L₀ e₀ → L₀.PhiFree i k

def XRegUnitOf : Prop :=
  ∀ (O : Type) [CommRing O] (B : Base O) (n : ℕ) (V₀ : Type) [AddCommGroup V₀]
    [Module (PowerSeries O) V₀] (L₀ : Lat B n V₀) (e₀ : V₀), IsUnitObj L₀ e₀ → L₀.XReg

def PhiXShapeOf : Prop :=
  ∀ (O : Type) [CommRing O] [IsLocalRing O] (B : Base O), 1 ≤ B.ℓ → ¬ IsUnit (B.ℓ : O) →
    IsAdicComplete (Ideal.span {(B.ℓ : O)}) O → B.E3 → ∀ k : ℕ,
    ∃ (E : Polynomial O) (u : PowerSeries O), E.Monic ∧ E.natDegree = B.ℓ ^ k ∧
      (∀ i < B.ℓ ^ k, (B.ℓ : O) ∣ E.coeff i) ∧ IsUnit u ∧
      (⇑B.φ)^[k] X = u * (E : PowerSeries O)

def PhiBasisOf : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (B : Base O), 1 ≤ B.ℓ →
    ¬ IsUnit (B.ℓ : O) → IsAdicComplete (Ideal.span {(B.ℓ : O)}) O → B.E3 → ∀ k, B.PhiBasis k

def PhiBasisOfMax : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (B : Base O), 1 ≤ B.ℓ →
    ¬ IsUnit (B.ℓ : O) → B.E3 → ∀ k, B.PhiBasis k

def SmallAll : Prop :=
  FactVvalOf ∧ FactVOf ∧ PPevalVal ∧ PPvalOf ∧ WinSum ∧ KapExpWin ∧ PPvalWin ∧ PPvalKap ∧
    PhiFreeOfBasis ∧ PhiFreeOf ∧ XRegUnitOf ∧ PhiXShapeOf ∧ PhiBasisOf ∧ PhiBasisOfMax

end Formalism.ExponentWindows.E
