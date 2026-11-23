import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsPeriodOn
import Development.AutomorphicSpectrum.Proofs.MetricProofs.UpVApply
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagDimensionIndexEquiv
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan
open GlobalTheory.CompanionTheory.Ar.PB.PFl

namespace GlobalTheory.CompanionTheory.Ar.PB.PFl.AllKept

variable {Ψ : Type} {N j : ℕ}

theorem stepOf_val' (N j : ℕ) (c : Fin N) :
    (stepOf N j c : ℕ) = if N - j ≤ (c : ℕ) then (c : ℕ) - (N - j) else (c : ℕ) + j := rfl

theorem stepOf_mem' (hj : j ≤ N) (c : Fin N) : c ∈ stepCols N j (stepOf N j c) := by
  have := c.2
  have hv := stepOf_val' N j c
  simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and]
  split_ifs at hv ⊢ <;> omega

theorem stepOf_top' (hj : j ≤ N) (c d : Fin N) (hd : d ∈ stepCols N j (stepOf N j c)) : d ≤ c := by
  have := c.2
  have := d.2
  have hv := stepOf_val' N j c
  simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and] at hd
  rw [Fin.le_def]
  split_ifs at hv hd <;> omega

theorem stepOf_proper' (hj : j ≤ N) {a b : Fin N} (hlt : b < a) (hblk : ((a : ℕ) < N - j ↔ (b : ℕ) < N - j)) :
    IsProperStep N j (stepOf N j b) := by
  have := a.2
  have := b.2
  have h : (b : ℕ) < a := hlt
  have hv := stepOf_val' N j b
  simp only [IsProperStep]
  split_ifs at hv <;> omega

theorem sep_of_all (hj : j ≤ N) {keep : Ψ × Fin N → Prop} (hk : ∀ p, keep p) (q : LowIdx Ψ N j) : Sep keep q :=
  ⟨stepOf N j q.1.2.2, hk _, stepOf_proper' hj q.2.1 q.2.2, stepOf_mem' hj _,
    fun h => absurd (stepOf_top' hj _ _ h) (not_le.2 q.2.1)⟩

theorem card_pIdx_of_all : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (keep : Ψ × Fin N → Prop), j ≤ N →
    (∀ p, keep p) → Nat.card (PIdx j keep) = Fintype.card Ψ * (j.choose 2 + (N - j).choose 2) := by
  intro Ψ _ _ N j keep hj hk
  have e : PIdx j keep ≃ LowIdx Ψ N j := Equiv.subtypeUnivEquiv (sep_of_all hj hk)
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, GlobalTheory.CompanionTheory.Ar.PB.WMan.ChartCount.card_lowIdx Ψ N j hj]

end GlobalTheory.CompanionTheory.Ar.PB.PFl.AllKept
