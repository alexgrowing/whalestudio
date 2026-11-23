import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsBaseChart
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan

namespace GlobalTheory.CompanionTheory.Ar.PB.WMan.ChartCount

theorem sum_range_eq_choose (m : ℕ) : ∑ i ∈ Finset.range m, i = m.choose 2 := by
  rw [Finset.sum_range_id, Nat.choose_two_right]

theorem card_row (N j : ℕ) (hj : j ≤ N) (a : Fin N) :
    Fintype.card {b : Fin N // b < a ∧ ((a : ℕ) < N - j ↔ (b : ℕ) < N - j)} =
      if (a : ℕ) < N - j then (a : ℕ) else (a : ℕ) - (N - j) := by
  rw [Fintype.card_subtype]
  have key : (Finset.univ.filter fun b : Fin N => b < a ∧ ((a : ℕ) < N - j ↔ (b : ℕ) < N - j)).map
      Fin.valEmbedding = Finset.Ico (if (a : ℕ) < N - j then 0 else N - j) (a : ℕ) := by
    ext x
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
      Fin.valEmbedding_apply, Finset.mem_Ico]
    constructor
    · rintro ⟨b, ⟨hba, hiff⟩, rfl⟩
      have hba' : (b : ℕ) < a := hba
      split_ifs with h
      · exact ⟨Nat.zero_le _, hba'⟩
      · exact ⟨Nat.le_of_not_lt (fun hb => h (hiff.mpr hb)), hba'⟩
    · rintro ⟨h1, h2⟩
      refine ⟨⟨x, lt_trans h2 a.isLt⟩, ⟨h2, ?_⟩, rfl⟩
      show (a : ℕ) < N - j ↔ x < N - j
      split_ifs at h1 with h
      · exact ⟨fun _ => lt_trans h2 h, fun _ => h⟩
      · exact ⟨fun h' => absurd h' h, fun h' => absurd h1 (Nat.not_le.mpr h')⟩
  rw [← Finset.card_map Fin.valEmbedding, key, Nat.card_Ico]
  split_ifs <;> simp

theorem card_pairs (N j : ℕ) (hj : j ≤ N) :
    Fintype.card {p : Fin N × Fin N // p.2 < p.1 ∧ ((p.1 : ℕ) < N - j ↔ (p.2 : ℕ) < N - j)} =
      j.choose 2 + (N - j).choose 2 := by
  rw [Fintype.card_congr (Equiv.subtypeProdEquivSigmaSubtype
      (fun (a b : Fin N) => b < a ∧ ((a : ℕ) < N - j ↔ (b : ℕ) < N - j))), Fintype.card_sigma]
  have h1 : ∀ a : Fin N, Fintype.card {b : Fin N // b < a ∧ ((a : ℕ) < N - j ↔ (b : ℕ) < N - j)} =
      if (a : ℕ) < N - j then (a : ℕ) else (a : ℕ) - (N - j) := card_row N j hj
  simp only [h1]
  have hs : ∑ a : Fin N, (if (a : ℕ) < N - j then (a : ℕ) else (a : ℕ) - (N - j)) =
      ∑ i ∈ Finset.range N, (if i < N - j then i else i - (N - j)) :=
    Fin.sum_univ_eq_sum_range (fun i => if i < N - j then i else i - (N - j)) N
  rw [hs]
  obtain ⟨M, rfl⟩ : ∃ M, N = M + j := ⟨N - j, by omega⟩
  have hM : M + j - j = M := by omega
  rw [hM, Finset.sum_range_add]
  have e1 : ∑ x ∈ Finset.range M, (if x < M then x else x - M) = ∑ x ∈ Finset.range M, x :=
    Finset.sum_congr rfl (fun x hx => if_pos (Finset.mem_range.mp hx))
  have e2 : ∑ x ∈ Finset.range j, (if M + x < M then M + x else M + x - M) =
      ∑ x ∈ Finset.range j, x :=
    Finset.sum_congr rfl (fun x _ => by rw [if_neg (by omega)]; omega)
  rw [e1, e2, sum_range_eq_choose, sum_range_eq_choose, add_comm]

theorem card_lowIdx (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (hj : j ≤ N) :
    Fintype.card (LowIdx Ψ N j) = Fintype.card Ψ * (j.choose 2 + (N - j).choose 2) := by
  rw [← card_pairs N j hj, ← Fintype.card_prod]
  exact Fintype.card_congr
    { toFun := fun q => (q.1.1, ⟨q.1.2, q.2⟩)
      invFun := fun x => ⟨(x.1, x.2.1), x.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

theorem nonempty_paramEquiv : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j n d : ℕ), j ≤ N →
    d + 1 = n + Fintype.card Ψ * (j.choose 2 + (N - j).choose 2) →
    Nonempty (Fin n ⊕ LowIdx Ψ N j ⊕ Unit ≃ Fin (d + 2)) := by
  intro Ψ _ _ N j n d hj hd
  apply Fintype.card_eq.mp
  rw [Fintype.card_sum, Fintype.card_sum, Fintype.card_fin, card_lowIdx Ψ N j hj,
    Fintype.card_unit, Fintype.card_fin]
  generalize Fintype.card Ψ * (j.choose 2 + (N - j).choose 2) = t at hd ⊢
  omega

end GlobalTheory.CompanionTheory.Ar.PB.WMan.ChartCount
