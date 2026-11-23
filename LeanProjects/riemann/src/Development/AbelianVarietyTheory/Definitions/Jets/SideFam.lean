import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPrAlt
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeries₂.DSExist
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeries₂.Zuckerman
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeries₂.Poulsen
import Formalism.PeriodIntegrals.DSInfCharCap
import Formalism.PeriodIntegrals.LowCyc
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.SubmatrixMemUJsetIff

open Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

noncomputable section

namespace BranchingSupport

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData

def Hyps : Prop :=
  ThreeDimData.Inputs ∧ PI.SmoothCyc ∧ PI.DSInfCharCap.DSInfCharCap ∧ DSExist ∧ Zuckerman ∧ Poulsen ∧
    GlobalTheory.FormalDegree.HarishChandra

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

def eZ {n : ℕ} (I : Finset (Fin n)) : Fin n → ℤ := fun i => if i ∈ I then 1 else 0

def n1 {n : ℕ} (x : Fin n → ℤ) : ℕ := ∑ i, (x i).natAbs

def IsCoef {k r : ℕ} (R : Rep k r) (l : R.H → Wp) (l' : R.H → Wq) (F : Mx k r → (Wq →L[ℂ] Wp)) (s : ℂ) : Prop :=
  ∃ (m : ℕ) (x y : Fin m → R.H) (X : Fin m → (Wq →L[ℂ] Wp)), (∀ i, x i ∈ R.TK ∧ y i ∈ R.TK) ∧
    (∀ g ∈ GG k r, F g = ∑ i, ⟪x i, R.σ g (y i)⟫_ℂ • X i) ∧ s = ∑ i, ⟪l (x i), X i (l' (y i))⟫_ℂ

def Hsq (r : ℕ) (T b : ℝ) : ℝ := max 1 T * b ^ (20 * (r + 1))

def SideFam {k r : ℕ} [CompleteSpace Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp))
    (μW μN μG : Measure (Formalism.QuantumDeterminants.Mt k r)) (q0 : ℕ) (R : (Fin (2 * r + k + 1) → ℤ) → Rep k r)
    (l : ∀ ν, (R ν).H → Wp) (dg : (Fin (2 * r + k + 1) → ℤ) → ℝ) : Prop :=
  ∀ ν, n1 ν ≤ q0 → IsBeL (R ν) z π μW μN (l ν) ∧ 0 < dg ν ∧
    ∀ w, w ≠ 0 → PI.BesselPeriodGGP.fdegH μG (R ν).σ w = dg ν

def Setup {k r : ℕ} [CompleteSpace Wp] (lam : Fin (2 * r + k + 1) → ℝ) (u : ℕ → ℝ) (b bv ga h : ℝ) (q0 : ℕ)
    (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r))
    (R : (Fin (2 * r + k + 1) → ℤ) → Rep k r) (l : ∀ ν, (R ν).H → Wp) (dg : (Fin (2 * r + k + 1) → ℤ) → ℝ) : Prop :=
  Num k r lam u b bv ga h q0 ∧ IsFam lam q0 R ∧ SideG k r z π u μW μN μG νq ∧ SideFam z π μW μN μG q0 R l dg

end BranchingSupport
