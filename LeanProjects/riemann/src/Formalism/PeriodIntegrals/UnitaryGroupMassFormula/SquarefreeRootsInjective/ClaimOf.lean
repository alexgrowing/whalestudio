import Formalism.PeriodIntegrals.SqfRootsInj

open Polynomial

noncomputable section

namespace PI.SqfRootsInj.W

open PI.SqfLab

def Lp (g e ℓ : ℕ) : ℕ := ℓ ^ padicValNat ℓ (g ^ e - 1)

def CaseA (g r ℓ : ℕ) [Fact g.Prime] (f : (ZMod g)[X]) : Prop :=
  ∃ (e j : ℕ) (w : Fbar g), 2 ≤ e ∧ e ≤ r ∧ 1 ≤ j ∧ 2 * j ≤ e ∧ ℓ ∣ g ^ e - 1 ∧
    (minpoly (ZMod g) w).natDegree = e ∧ minpoly (ZMod g) w ∣ f ∧
    w ^ ((g ^ j - 1) * Lp g e ℓ) = 1

def CaseB (g r ℓ : ℕ) [Fact g.Prime] (f : (ZMod g)[X]) : Prop :=
  ∃ (e e' : ℕ) (x y : Fbar g), 1 ≤ e' ∧ e' ≤ e ∧ e + e' ≤ r ∧
    ℓ ∣ (g ^ e - 1) * (g ^ e' - 1) ∧
    (minpoly (ZMod g) x).natDegree = e ∧ (minpoly (ZMod g) y).natDegree = e' ∧
    minpoly (ZMod g) x * minpoly (ZMod g) y ∣ f ∧ y ^ (g ^ e') = y ∧
    x ^ Lp g e ℓ = (primeToPart ℓ y) ^ Lp g e ℓ

def Witness : Prop :=
  ∀ (g r : ℕ) [Fact g.Prime] (f : (ZMod g)[X]), Eii g r f →
    ∃ ℓ : ℕ, ℓ.Prime ∧ ℓ ∉ BB r g ∧ (CaseA g r ℓ f ∨ CaseB g r ℓ f)

def Count : Prop :=
  ∀ (g r : ℕ) [Fact g.Prime], 100 ≤ r → 2 ^ 12 ≤ g →
    ∀ T : Finset (ZMod g)[X],
      (∀ f ∈ T, IsLab g r f ∧ ∃ ℓ : ℕ, ℓ.Prime ∧ ℓ ∉ BB r g ∧ (CaseA g r ℓ f ∨ CaseB g r ℓ f)) →
      (T.card : ℝ) ≤ 23 * Real.log g * (g : ℝ) ^ (-(1 / 2 : ℝ)) * (g : ℝ) ^ r

theorem claim_of (h1 : Witness) (h2 : Count) : PI.SqfRootsInj.Claim := by
  intro g r _ hr hg T hT
  exact h2 g r hr hg T fun f hf => ⟨(hT f hf).1, h1 g r f (hT f hf)⟩

end PI.SqfRootsInj.W
