import Formalism.LocalToGlobal.Columns.ReferenceActionRationalLevels
import Formalism.LocalToGlobal.Columns.InputsWeyl
import Formalism.LocalToGlobal.Columns.BrwLastNeZero
import Formalism.GL3MeanSquares.UnitaryConjugateDiagonalMoments

open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.ColOpen

open Formalism.BasicNotions Formalism.L2.Col Formalism.LogVandermondeBounds.StandardLattice Formalism.HermitianLattices.FormalDegreeBoundsAlt

variable {X : Fields} {Pr : Primes X} {R : Ranks}

section Seq

variable (W : Wts X Pr.Word R)

def vSeq (τ : X.Tau) : ℕ → ℝ := fun i => if h : i < R.k - 1 then (((W.row τ).v ⟨i, h⟩ : ℚ) : ℝ) else 0

def bSeq (τ : X.Tau) : ℕ → ℝ := fun j => (((W.row τ).bAt j : ℚ) : ℝ)

def eSeq (τ : X.Tau) : ℕ → ℝ := fun j => (((W.row τ).eAt j : ℚ) : ℝ)

def lamSeq (τ : X.Tau) : ℕ → ℝ := rowPar R.k (vSeq W τ) (bSeq W τ)

end Seq

structure Grid (W : Wts X Pr.Word R) (Δ S : ℝ) (c : X.Tau → ℝ) (code : Pr.Word → ℕ → ℕ) : Prop where
  one_le_Δ : 1 ≤ Δ
  S_eq : S = (R.k : ℝ) * (4 * Δ)
  cloud : ∀ τ i, i < R.k - 1 → vSeq W τ i = cloudV (c τ) Δ i
  cloud_nonneg : ∀ τ i, i < R.k - 1 → 0 ≤ vSeq W τ i
  cloud_le : ∀ τ i, i < R.k - 1 → vSeq W τ i ≤ S
  word : ∀ u τ l, l < R.k - 2 → hcSeq W u τ (l + 1) = vSeq W τ l - 1 / 2 - (code u l : ℝ) * Δ
  code_le : ∀ u l, code u l ≤ 1

structure Ends (W : Wts X Pr.Word R) (a b' S : ℝ) : Prop where
  top : ∀ u, ∀ τ ∈ W.tops, a ≤ (W.aTop u τ : ℝ) ∧ (W.aTop u τ : ℝ) ≤ a * (1 + 1 / (R.k : ℝ)) ∧
    b' ≤ (W.bTop u τ : ℝ) ∧ (W.bTop u τ : ℝ) ≤ 2 * b'
  b'_le : 2 * b' ≤ a / 4
  oth_first : ∀ u τ, τ ∉ W.tops → S ≤ hcSeq W u τ 0 - vSeq W τ 0 ∧ hcSeq W u τ 0 - vSeq W τ 0 ≤ 2 * S
  oth_last : ∀ u τ, τ ∉ W.tops → hcSeq W u τ (R.k - 1) = vSeq W τ (R.k - 2) - 1 / 2
  kS_le : (R.k : ℝ) * S ≤ b'

structure Nodes (W : Wts X Pr.Word R) (x L eta S : ℝ) : Prop where
  b_ge : ∀ τ j, j < R.m → 1 ≤ bSeq W τ j
  b_log : ∀ τ j, j < R.m → Real.log (bSeq W τ j) ≤ 2 * L
  e_le : ∀ τ j, j < R.m → eSeq W τ j - bSeq W τ j ≤ eta
  eta_le : ∀ τ j, j < R.m → eta ≤ bSeq W τ j / x
  S_le : ∀ τ j, j < R.m → S ≤ bSeq W τ j / x

variable (X Pr R) in

structure Nums5 (n : ScNum) : Prop where
  pi_le_v : Real.pi ≤ vC X
  log_2v : Real.log (2 * vC X) ≤ n.sc.L
  log_g : ∀ i, Real.log (Pr.g i) ≤ n.CY * n.sc.L
  m_ge : 44 ≤ R.m
  m_le_alt : (R.m : ℝ) ≤ n.sc.x
  log_2k : Real.log (2 * (R.k : ℝ)) ≤ n.sc.L
  log_2a : Real.log (2 * n.sc.a) ≤ 2 * n.sc.L
  log_S : Real.log n.Sc ≤ n.sc.L

def DsigLow (W : Wts X Pr.Word R) (dsig : X.Tau → ℝ) : Prop :=
  ∀ τ, (1 - 1 / 3 : ℝ) * dimVN (lamSeq W τ) (R.k - 1 + R.m) ≤ dsig τ

def DsigUp (W : Wts X Pr.Word R) (dsig : X.Tau → ℝ) : Prop :=
  ∀ τ, dsig τ ≤ 4 * dTau R.k R.m (lamSeq W τ) *
    (3 * (((R.k - 1 + R.m / 2) * (R.m / 2) : ℕ) : ℝ) * (vSeq W τ 0 + bSeq W τ (R.m - 1))) ^ ((R.k - 1 + R.m / 2) * (R.m / 2))

end Formalism.L2.GlobalTheoryTheory.ColOpen
