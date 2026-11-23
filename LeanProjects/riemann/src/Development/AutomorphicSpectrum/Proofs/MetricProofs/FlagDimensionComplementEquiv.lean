import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.BasePartFlagPt
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagDimensionIndexEquiv
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.Coord

theorem nat_card_cIdx (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (τ : Ψ) (ca cb : Fin N) (hj : j ≤ N)
    (hab : ca < cb) (hblk : (cb : ℕ) < N - j ↔ (ca : ℕ) < N - j) :
    Nat.card (FC.CIdx Ψ N j τ ca cb) + 1 = Fintype.card Ψ * (j.choose 2 + (N - j).choose 2) := by
  classical
  obtain ⟨q0, hq0⟩ : ∃ q0 : LowIdx Ψ N j, q0.1 = (τ, cb, ca) := ⟨⟨(τ, cb, ca), hab, hblk⟩, rfl⟩
  have e : FC.CIdx Ψ N j τ ca cb ≃ {q : LowIdx Ψ N j // q ≠ q0} :=
    Equiv.subtypeEquivRight (fun q => by
      show q.1 ≠ (τ, cb, ca) ↔ q ≠ q0
      rw [← hq0]
      exact not_congr Subtype.ext_iff.symm)
  have h1 : Nat.card (Option {q : LowIdx Ψ N j // q ≠ q0}) = Nat.card (LowIdx Ψ N j) :=
    Nat.card_congr (Equiv.optionSubtypeNe q0)
  rw [Nat.card_eq_fintype_card, Fintype.card_option] at h1
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, h1, Nat.card_eq_fintype_card]
  convert GlobalTheory.CompanionTheory.Ar.PB.WMan.ChartCount.card_lowIdx Ψ N j hj

theorem nonempty_equiv_cIdx : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j n d : ℕ) (τ : Ψ) (ca cb : Fin N), j ≤ N →
    ca < cb → ((cb : ℕ) < N - j ↔ (ca : ℕ) < N - j) →
    d + 1 = n + Fintype.card Ψ * (j.choose 2 + (N - j).choose 2) →
    Nonempty (Fin d ≃ Fin n ⊕ FC.CIdx Ψ N j τ ca cb) := by
  intro Ψ _ _ N j n d τ ca cb hj hab hblk hd
  have h := nat_card_cIdx Ψ N j τ ca cb hj hab hblk
  apply Finite.card_eq.1
  rw [Nat.card_sum, Nat.card_eq_fintype_card (α := Fin d), Fintype.card_fin,
    Nat.card_eq_fintype_card (α := Fin n), Fintype.card_fin]
  omega

end GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.Coord
