import Mathlib
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ModelLeaves

noncomputable section

universe u

structure FrobeniusScaling (ι : Type u) where

  φ : Equiv.Perm ι

  p : ℕ
  two_le_p : 2 ≤ p

  d : ι → ℝ
  scaling : ∀ σ, d (φ σ) = (p : ℝ) * d σ

def FrobeniusDegreeZero.Statement : Prop :=
  ∀ (ι : Type u) [Finite ι] (D : FrobeniusScaling ι), D.d = 0

structure TrivialFlagRoots (R : Type u) [CommRing R] (N : ℕ) where

  x : Fin N → R
  esymm_eval_eq_zero : ∀ j : ℕ, 1 ≤ j → MvPolynomial.eval x (MvPolynomial.esymm (Fin N) R j) = 0

def TrivialFlagPowerSums.Statement : Prop :=
  ∀ (R : Type u) [CommRing R] (N : ℕ) (F : TrivialFlagRoots R N) (k : ℕ), 1 ≤ k →
    ∑ i, F.x i ^ k = 0

structure CyclicRecursionData (ι : Type u) where

  φ : Equiv.Perm ι

  q : ℝ
  q_pos : 0 < q
  q_lt_one : q < 1

  h : ι → ℝ

  lam : ι → ℝ
  recursion : ∀ τ, h τ = q * (lam (φ τ) + h (φ τ))

def CyclicRecursion.Statement : Prop :=
  ∀ (ι : Type u) [Finite ι] (C : CyclicRecursionData ι) (τ : ι),
    HasSum (fun n : ℕ => C.q ^ (n + 1) * C.lam ((C.φ ^ (n + 1)) τ)) (C.h τ)

structure FrobeniusRecursionData (ι : Type u) extends CyclicRecursionData ι where

  p : ℕ

  k : ℕ
  two_le_p : 2 ≤ p
  one_le_k : 1 ≤ k
  q_eq : q = 1 / (p : ℝ) ^ k

def returnTerm {ι : Type u} [DecidableEq ι] (φ : Equiv.Perm ι) (p k : ℕ) (τ σ : ι) (n : ℕ) : ℝ :=
  if (φ ^ (n + 1)) τ = σ then (1 / (p : ℝ) ^ k) ^ (n + 1) else 0

def co {ι : Type u} [DecidableEq ι] (φ : Equiv.Perm ι) (p k : ℕ) (τ σ : ι) : ℝ :=
  (∑' n : ℕ, returnTerm φ p k τ σ n) - (if σ = τ then 1 / ((p : ℝ) - 1) else 0)

def CoefficientFormula.Statement : Prop :=
  ∀ (ι : Type u) [Fintype ι] [DecidableEq ι] (C : FrobeniusRecursionData ι) (τ : ι),
    (∀ σ, Summable (returnTerm C.φ C.p C.k τ σ)) ∧
      C.h τ - C.lam τ / ((C.p : ℝ) - 1) = ∑ σ, co C.φ C.p C.k τ σ * C.lam σ

def ConstantCase.Statement : Prop :=
  ∀ (ι : Type u) [Finite ι] (C : FrobeniusRecursionData ι) (La : ℝ), (∀ σ, C.lam σ = La) →
    ∀ τ, C.h τ = La / ((C.p : ℝ) ^ C.k - 1)

def FrobeniusScaling.exampleZMod3 : FrobeniusScaling (ZMod 3) where
  φ := Equiv.addRight 1
  p := 2
  two_le_p := le_rfl
  d := 0
  scaling := fun _ => by simp

def TrivialFlagRoots.exampleZMod4 : TrivialFlagRoots (ZMod 4) 2 where
  x := ![2, 2]
  esymm_eval_eq_zero := by
    intro j hj
    rw [MvPolynomial.esymm, map_sum]
    simp only [map_prod, MvPolynomial.eval_X]
    match j, hj with
    | 1, _ => decide
    | 2, _ => decide
    | j + 3, _ =>
      rw [Finset.powersetCard_eq_empty.mpr (by simp)]
      simp

theorem TrivialFlagRoots.exampleZMod4_x_ne_zero : TrivialFlagRoots.exampleZMod4.x ≠ 0 := by
  intro h
  have := congrFun h 0
  revert this
  decide

def CyclicRecursionData.exampleZMod2 : CyclicRecursionData (ZMod 2) where
  φ := Equiv.addRight 1
  q := 1 / 2
  q_pos := by norm_num
  q_lt_one := by norm_num
  h := fun σ => if σ = 0 then 2 else 1
  lam := fun σ => if σ = 0 then 0 else 3
  recursion := by
    intro τ
    rcases (by decide : ∀ σ : ZMod 2, σ = 0 ∨ σ = 1) τ with rfl | rfl
    · simp [show (1 : ZMod 2) ≠ 0 by decide]
      norm_num
    · simp [show (1 : ZMod 2) ≠ 0 by decide, show (1 : ZMod 2) + 1 = 0 by decide]

theorem CyclicRecursionData.exampleZMod2_lam_nonconstant :
    CyclicRecursionData.exampleZMod2.lam 0 ≠ CyclicRecursionData.exampleZMod2.lam 1 := by
  simp [CyclicRecursionData.exampleZMod2, show (1 : ZMod 2) ≠ 0 by decide]

def FrobeniusRecursionData.exampleZMod2 : FrobeniusRecursionData (ZMod 2) where
  toCyclicRecursionData := CyclicRecursionData.exampleZMod2
  p := 2
  k := 1
  two_le_p := le_rfl
  one_le_k := le_rfl
  q_eq := by simp [CyclicRecursionData.exampleZMod2]

def FrobeniusRecursionData.exampleConstant : FrobeniusRecursionData (ZMod 3) where
  φ := Equiv.addRight 1
  q := 1 / 3
  q_pos := by norm_num
  q_lt_one := by norm_num
  h := fun _ => 1
  lam := fun _ => 2
  recursion := fun _ => by norm_num
  p := 3
  k := 1
  two_le_p := by norm_num
  one_le_k := le_rfl
  q_eq := by norm_num

theorem FrobeniusRecursionData.exampleConstant_hyp :
    ∀ σ, FrobeniusRecursionData.exampleConstant.lam σ = 2 := fun _ => rfl

end

end GroundTheory.Heights₂.Heights.ModelLeaves
