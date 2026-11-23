import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.SimilitudeFactorFormGroupBoundedOfTestSupport

noncomputable section

open Classical

namespace GlobalTheory.CompanionTheory.Ar.Cmp.FlagCst

open GlobalTheory.CompanionTheory.Ar.Cmp

def relab (N j : ℕ) (a : Fin N) : ℕ := if (a : ℕ) < N - j then j + a else a - (N - j)

def Sep {Ψ : Type} (N j : ℕ) (x : Ψ × Fin N) (c : LowEnt Ψ N) : Prop :=
  c.1 = x.1 ∧ min (relab N j c.2.1.1) (relab N j c.2.1.2) ≤ (x.2 : ℕ) ∧
    (x.2 : ℕ) < max (relab N j c.2.1.1) (relab N j c.2.1.2)

def sepCount {Ψ : Type} [Fintype Ψ] {e : ℕ} (N j : ℕ) (w : Fin e → Ψ × Fin N) : ℝ :=
  ∑ f : LowEnt Ψ N ≃ Fin e, ∏ c : LowEnt Ψ N, if Sep N j (w (f c)) c then (1 : ℝ) else 0

theorem relab_self (N : ℕ) (a : Fin N) : relab N N a = a := by
  simp [relab]

theorem sepCount_nonneg {Ψ : Type} [Fintype Ψ] {e : ℕ} (N j : ℕ) (w : Fin e → Ψ × Fin N) :
    0 ≤ sepCount N j w :=
  Finset.sum_nonneg fun _ _ => Finset.prod_nonneg fun _ _ => by split_ifs <;> norm_num

end GlobalTheory.CompanionTheory.Ar.Cmp.FlagCst
