import Mathlib

noncomputable section
open scoped BigOperators Classical

namespace Formalism.L2.Th1.CM

def omegaK (d : ℕ) : ℂ := (1 + Complex.I * ((Real.sqrt d : ℝ) : ℂ)) / 2

def HasCMBy (d : ℕ) (L : PeriodPair) : Prop := ∀ ω ∈ L.lattice, omegaK d * ω ∈ L.lattice

def jInv (L : PeriodPair) : ℂ := 1728 * L.g₂ ^ 3 / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2)

def MaximalUnramifiedExtension (l : ℕ) [Fact l.Prime] : Subfield ℂ_[l] :=
  (Subfield.closure {ζ : ℂ_[l] | ∃ n : ℕ, 0 < n ∧ ¬ l ∣ n ∧ ζ ^ n = 1}).topologicalClosure

def cW {K : Type} [Field K] (g2 g3 : K) (k : ℕ) : K :=
  Nat.strongRecOn k (fun k ih =>
    if k = 2 then g2 / 20 else if k = 3 then g3 / 28 else
    if h : 4 ≤ k then
      3 / ((2 * (k : K) + 1) * ((k : K) - 3)) *
        ∑ m : Fin (k - 3), ih (m.val + 2) (by omega) * ih (k - (m.val + 2)) (by omega)
    else 0)

def wpNum {K : Type} [Field K] (g2 g3 : K) : PowerSeries K :=
  PowerSeries.mk fun n => if n = 0 then 1 else if Even n then cW g2 g3 (n / 2) else 0

def wpDen {K : Type} [Field K] (g2 g3 : K) : PowerSeries K :=
  PowerSeries.mk fun n => if n = 0 then 1 else
    if Even n then -(((n / 2 : ℕ) : K) - 1) * cW g2 g3 (n / 2) else 0

def uSer {K : Type} [Field K] (g2 g3 : K) : PowerSeries K :=
  PowerSeries.X * wpNum g2 g3 * (wpDen g2 g3)⁻¹

def ltLog (K : Type) [Field K] (l : ℕ) : PowerSeries K :=
  PowerSeries.mk fun n => if h : ∃ j : ℕ, n = (l ^ 2) ^ j then ((l : K) ^ (Nat.find h))⁻¹ else 0

def IsGoodModel (l : ℕ) [Fact l.Prime] (L : PeriodPair) (ι : ℂ ≃+* ℂ_[l]) (g2 g3 : ℂ_[l]) : Prop :=
  g2 ∈ MaximalUnramifiedExtension l ∧ g3 ∈ MaximalUnramifiedExtension l ∧ ‖g2‖ ≤ 1 ∧ ‖g3‖ ≤ 1 ∧ ‖g2 ^ 3 - 27 * g3 ^ 2‖ = 1 ∧
    ∃ lam : ℂ_[l], lam ≠ 0 ∧ g2 = lam ^ 4 * ι L.g₂ ∧ g3 = lam ^ 6 * ι L.g₃

def JInvariantIntegrality : Prop :=
  ∀ (d : ℕ) (L : PeriodPair), Squarefree d → d % 4 = 3 → HasCMBy d L → IsIntegral ℤ (jInv L)

def CM2 : Prop :=
  ∀ (d : ℕ) (L : PeriodPair), Squarefree d → d % 4 = 3 → HasCMBy d L →
    ∀ (l : ℕ) [Fact l.Prime], 5 ≤ l → ¬ l ∣ d → ∀ ι : ℂ ≃+* ℂ_[l], ∃ g2 g3, IsGoodModel l L ι g2 g3

def CM3 : Prop :=
  ∀ (d : ℕ) (L : PeriodPair), Squarefree d → d % 4 = 3 → HasCMBy d L →
    ∀ (l : ℕ) [Fact l.Prime], 5 ≤ l → ¬ l ∣ d → (¬ ∃ a : ZMod l, a ^ 2 = -(d : ZMod l)) →
    ∀ (ι : ℂ ≃+* ℂ_[l]) (g2 g3 : ℂ_[l]), IsGoodModel l L ι g2 g3 →
      ∃ ε ∈ MaximalUnramifiedExtension l, ‖ε‖ = 1 ∧ ∀ n : ℕ,
        PowerSeries.coeff n ((uSer g2 g3).subst (PowerSeries.C ε * ltLog ℂ_[l] l)) ∈ MaximalUnramifiedExtension l ∧
        ‖PowerSeries.coeff n ((uSer g2 g3).subst (PowerSeries.C ε * ltLog ℂ_[l] l))‖ ≤ 1

end Formalism.L2.Th1.CM
