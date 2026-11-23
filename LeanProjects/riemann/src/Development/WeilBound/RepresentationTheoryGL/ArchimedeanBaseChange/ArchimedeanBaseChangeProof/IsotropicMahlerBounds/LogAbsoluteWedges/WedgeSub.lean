import Mathlib

noncomputable section

open Matrix

namespace PositivityTheory.Rg.BcB.D1

def nF {K ι κ : Type} [NormedField K] [Fintype κ] [DecidableEq κ] (A : Matrix ι κ K) : ℝ :=
  ⨆ s : κ → ι, ‖(A.submatrix s id).det‖

def nI {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq κ] (A : Matrix ι κ ℂ) : ℝ := ((Aᴴ * A).det).re

def sz {K ι κ : Type} [NormedField K] (g : Matrix ι κ K) : ℝ := ⨆ p : ι × κ, ‖g p.1 p.2‖

abbrev Fam (K ι : Type) : Type 1 := ∀ (κ : Type) [Fintype κ] [DecidableEq κ], Matrix ι κ K → ℝ

structure IsWedge {K ι : Type} [Field K] [Fintype ι] [DecidableEq ι] (N : Fam K ι) : Prop where
  nonneg : ∀ (κ : Type) [Fintype κ] [DecidableEq κ] (A : Matrix ι κ K), 0 ≤ N κ A
  ne_zero : ∀ (κ : Type) [Fintype κ] [DecidableEq κ] (A : Matrix ι κ K), N κ A ≠ 0 ↔ LinearIndependent K Aᵀ
  reindex : ∀ (κ κ' : Type) [Fintype κ] [DecidableEq κ] [Fintype κ'] [DecidableEq κ'] (e : κ' ≃ κ) (A : Matrix ι κ K),
    N κ' (A.submatrix id e) = N κ A
  quot : ∀ (κ : Type) [Fintype κ] [DecidableEq κ] (B : Matrix ι κ K), LinearIndependent K Bᵀ →
    ∃ Y : Matrix κ ι K, ∀ (κ' : Type) [Fintype κ'] [DecidableEq κ'] (C : Matrix ι κ' K),
      N (κ ⊕ κ') (fromCols B C) = N κ B * N κ' ((1 - B * Y) * C) ∧ N κ' ((1 - B * Y) * C) ≤ N κ' C ∧ (1 - B * Y) * B = 0

def WedgeF : Prop := ∀ (K ι : Type) [NormedField K] [IsUltrametricDist K] [Fintype ι] [DecidableEq ι],
  IsWedge (K := K) (ι := ι) fun _ _ _ A => nF A

def WedgeI : Prop := ∀ (ι : Type) [Fintype ι] [DecidableEq ι], IsWedge (K := ℂ) (ι := ι) fun _ _ _ A => nI A

def WedgeSub : Prop := ∀ (K ι : Type) [Field K] [Fintype ι] [DecidableEq ι] (N : Fam K ι), IsWedge N →
  ∀ (κ₀ κ₁ κ₂ : Type) [Fintype κ₀] [DecidableEq κ₀] [Fintype κ₁] [DecidableEq κ₁] [Fintype κ₂] [DecidableEq κ₂]
    (B : Matrix ι κ₀ K) (A : Matrix ι κ₁ K) (C : Matrix ι κ₂ K),
    N (κ₀ ⊕ (κ₁ ⊕ κ₂)) (fromCols B (fromCols A C)) * N κ₀ B ≤
      N (κ₀ ⊕ κ₁) (fromCols B A) * N (κ₀ ⊕ κ₂) (fromCols B C)

def MulF : Prop := ∀ (K ι ι' κ : Type) [NormedField K] [IsUltrametricDist K] [Fintype ι] [Fintype ι'] [Fintype κ]
  [DecidableEq κ] (A : Matrix ι κ K),
    (∀ g : Matrix ι' ι K, nF (g * A) ≤ sz g ^ Fintype.card κ * nF A) ∧ (∀ s : Matrix κ κ K, nF (A * s) = nF A * ‖s.det‖) ∧
    ∀ s : Matrix κ κ K, nF s = ‖s.det‖

def DetMono : Prop := ∀ (κ : Type) [Fintype κ] [DecidableEq κ] (X Y : Matrix κ κ ℂ),
  open ComplexOrder in X.PosSemidef → (Y - X).PosSemidef → X.det.re ≤ Y.det.re

def MulI : Prop := ∀ (ι ι' κ : Type) [Fintype ι] [Fintype ι'] [Fintype κ] [DecidableEq κ] (A : Matrix ι κ ℂ),
    (∀ g : Matrix ι' ι ℂ, nI (g * A) ≤ ((Fintype.card ι * Fintype.card ι' : ℝ) * sz g ^ 2) ^ Fintype.card κ * nI A) ∧
    (∀ s : Matrix κ κ ℂ, nI (A * s) = nI A * ‖s.det‖ ^ 2) ∧ ∀ s : Matrix κ κ ℂ, nI s = ‖s.det‖ ^ 2

def PairF : Prop := ∀ (K ι κ : Type) [NormedField K] [IsUltrametricDist K] [Fintype ι] [Fintype κ] [DecidableEq κ]
  (U W : Matrix ι κ K), ‖(Uᵀ * W).det‖ ≤ nF U * nF W

def PairI : Prop := ∀ (ι κ : Type) [Fintype ι] [Fintype κ] [DecidableEq κ] (U W : Matrix ι κ ℂ),
  ‖(Uᴴ * W).det‖ ^ 2 ≤ nI U * nI W

example : nF (1 : Matrix (Fin 0) (Fin 0) ℝ) = 1 := by simp [nF]

end PositivityTheory.Rg.BcB.D1

end
