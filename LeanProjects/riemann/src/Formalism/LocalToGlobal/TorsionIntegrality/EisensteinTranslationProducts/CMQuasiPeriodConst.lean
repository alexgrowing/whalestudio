import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.TranslateProduct

noncomputable section
open scoped BigOperators ComplexConjugate

namespace Formalism.L2.Th1.F

def cmTheta (b : ℤ) (d : ℕ) : ℂ := ((b : ℂ) + Complex.I * ((Real.sqrt d : ℝ) : ℂ)) / 2

def cmPair (a : ℕ) (b : ℤ) (d : ℕ) (ha : 0 < a) (hd : 0 < d) : PeriodPair where
  ω₁ := (a : ℂ)
  ω₂ := cmTheta b d
  indep := by
    rw [LinearIndependent.pair_iff]
    intro s t h
    have hs : 0 < Real.sqrt d := Real.sqrt_pos.mpr (by exact_mod_cast hd)
    have him := congrArg Complex.im h
    have hre := congrArg Complex.re h
    simp [cmTheta] at him hre
    have ht : t = 0 := by
      rcases him with h1 | h1
      · exact h1
      · exact absurd h1 (by positivity)
    subst ht
    simp at hre
    refine ⟨?_, rfl⟩
    rcases hre with h1 | h1
    · exact h1
    · exact absurd h1 (by positivity)

def cmForm (a b c m n : ℤ) : ℤ := a * m ^ 2 + b * m * n + c * n ^ 2

def CmThetaEq : Prop :=
  ∀ (a : ℕ) (b c : ℤ) (d : ℕ), 4 * (a : ℤ) * c = b ^ 2 + d →
    cmTheta b d ^ 2 = (b : ℂ) * cmTheta b d - (a : ℂ) * (c : ℂ) ∧
    cmTheta b d + conj (cmTheta b d) = (b : ℂ) ∧ cmTheta b d * conj (cmTheta b d) = (a : ℂ) * (c : ℂ)

def CmStable : Prop :=
  ∀ (a : ℕ) (b c : ℤ) (d : ℕ) (ha : 0 < a) (hd : 0 < d), 4 * (a : ℤ) * c = b ^ 2 + d →
    ∀ m n : ℤ, MulStable (cmPair a b d ha hd) ((m : ℂ) + (n : ℂ) * cmTheta b d)

def CmOrder : Prop :=
  ∀ (a : ℕ) (b c : ℤ) (d : ℕ) (ha : 0 < a) (hd : 0 < d), 4 * (a : ℤ) * c = b ^ 2 + d →
    Int.gcd (Int.gcd a b) c = 1 → ∀ α : ℂ, MulStable (cmPair a b d ha hd) α →
      ∃ m n : ℤ, α = (m : ℂ) + (n : ℂ) * cmTheta b d

def CmArea : Prop :=
  ∀ (a : ℕ) (b : ℤ) (d : ℕ) (ha : 0 < a) (hd : 0 < d),
    area (cmPair a b d ha hd) = (a : ℝ) * Real.sqrt d / 2

def CmNorm : Prop :=
  ∀ (a : ℕ) (b c : ℤ) (d : ℕ) (ha : 0 < a) (hd : 0 < d), 4 * (a : ℤ) * c = b ^ 2 + d → ∀ m n : ℤ,
    Complex.normSq ((m : ℂ) * (a : ℂ) + (n : ℂ) * cmTheta b d) = (a : ℝ) * (cmForm a b c m n : ℝ) ∧
    herm (cmPair a b d ha hd) ((m : ℂ) * (a : ℂ) + (n : ℂ) * cmTheta b d)
        ((m : ℂ) * (a : ℂ) + (n : ℂ) * cmTheta b d)
      = ((2 * (cmForm a b c m n : ℝ) / Real.sqrt d : ℝ) : ℂ) ∧
    ((m, n) ≠ (0, 0) → 1 ≤ cmForm a b c m n)

def CmAltE : Prop :=
  ∀ (a : ℕ) (b : ℤ) (d : ℕ) (ha : 0 < a) (hd : 0 < d) (m n m' n' : ℤ),
    altE (cmPair a b d ha hd) ((m : ℂ) * (a : ℂ) + (n : ℂ) * cmTheta b d)
      ((m' : ℂ) * (a : ℂ) + (n' : ℂ) * cmTheta b d) = ((n * m' - m * n' : ℤ) : ℝ)

def CMHalfLatticeIff : Prop :=
  ∀ (a : ℕ) (b : ℤ) (d : ℕ) (ha : 0 < a) (hd : 0 < d), Odd a → ∀ m n : ℤ,
    (((m : ℂ) + (n : ℂ) * cmTheta b d) * ((a : ℂ) / 2) ∈ (cmPair a b d ha hd).lattice ↔
      Even m ∧ Even n)

def CmTheta0 : Prop :=
  ∀ (a : ℕ) (b c : ℤ) (d : ℕ) (ha : 0 < a) (hd : 0 < d), 4 * (a : ℤ) * c = b ^ 2 + d → Odd a →
    d % 8 = 7 → ∀ (m n : ℤ) (z : ℂ),
      th0 (cmPair a b d ha hd) ((a : ℂ) / 2) (z + ((m : ℂ) * (a : ℂ) + (n : ℂ) * cmTheta b d))
        = (-1 : ℂ) ^ (cmForm a b c m n).natAbs
          * Complex.exp ((Real.pi : ℂ) * herm (cmPair a b d ha hd) z
                ((m : ℂ) * (a : ℂ) + (n : ℂ) * cmTheta b d)
              + (Real.pi : ℂ) * herm (cmPair a b d ha hd) ((m : ℂ) * (a : ℂ) + (n : ℂ) * cmTheta b d)
                ((m : ℂ) * (a : ℂ) + (n : ℂ) * cmTheta b d) / 2)
          * th0 (cmPair a b d ha hd) ((a : ℂ) / 2) z

def CMQuasiPeriodConst : Prop :=
  ∀ (L : PeriodPair) (α : ℂ) (S : Finset ℂ), MulStable L α → α.im ≠ 0 → IsKerReps L α S →
    s2 L = (∑ P ∈ S, L.weierstrassP P) / (α * (α - conj α))

end Formalism.L2.Th1.F
