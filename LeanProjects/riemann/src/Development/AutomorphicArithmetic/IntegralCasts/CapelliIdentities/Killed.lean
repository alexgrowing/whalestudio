import Mathlib

theorem UpperTheory.Reformulated.B.Qe12.killed :
    ∀ (l : ℕ) [inst : Fact (Nat.Prime l)] (M : Type)
    [inst_1 : AddCommGroup M] [inst_2 : _root_.Module ℤ_[l] M] [Finite M],
    ∃ (r : ℕ), (0 : ℕ) < r ∧ ∀ (x : M), (↑l : ℤ_[l]) ^ r • x = (0 : M) := by
  intro l _ M _ _ _
  have hN : ((Nat.card M : ℕ) : ℤ_[l]) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  refine ⟨((Nat.card M : ℕ) : ℤ_[l]).valuation + 1, Nat.succ_pos _, fun x => ?_⟩
  have h1 : ((Nat.card M : ℕ) : ℤ_[l]) • x = 0 := by
    rw [Nat.cast_smul_eq_nsmul]
    exact card_nsmul_eq_zero'
  have h2 : ((PadicInt.unitCoeff hN : ℤ_[l]ˣ) : ℤ_[l]) •
      ((l : ℤ_[l]) ^ ((Nat.card M : ℕ) : ℤ_[l]).valuation • x) = 0 := by
    rw [← mul_smul, ← PadicInt.unitCoeff_spec hN]
    exact h1
  have h3 : (l : ℤ_[l]) ^ ((Nat.card M : ℕ) : ℤ_[l]).valuation • x = 0 :=
    ((PadicInt.unitCoeff hN).isUnit.smul_eq_zero).mp h2
  rw [pow_succ', mul_smul, h3, smul_zero]
