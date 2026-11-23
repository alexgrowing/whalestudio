import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MeasurePreservingMulRight
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqBotOrTopOfTensor
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.FiniteIntertwining

open MvPolynomial Formalism.BasicNotions Formalism.L2.DIV GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries GlobalTheory.ChiGrid GlobalTheory.RowReal
open Formalism.BasicNotions.TH Formalism.L2.Theta

namespace GlobalTheory.RowReal.WeightsX

open GlobalTheory.SignedHC

theorem mem_listBlock_iff {c x : ℚ} {n : ℕ} : x ∈ GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries.block c n ↔ x ∈ TPar.block c n := by
  rw [GlobalTheory.SignedHC.mem_block]
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries.block, List.mem_map, List.mem_range]
  exact ⟨fun ⟨a, h, e⟩ => ⟨a, h, e.symm⟩, fun ⟨a, h, e⟩ => ⟨a, h, e.symm⟩⟩

theorem pairwise_listBlock (c : ℚ) (n : ℕ) : (GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries.block c n).Pairwise (· > ·) := by
  unfold GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries.block
  rw [List.pairwise_map]
  refine (List.pairwise_lt_range (n := n)).imp fun {a b} h => ?_
  have : (a : ℚ) < b := by exact_mod_cast h
  linarith

theorem psiPar_eq (D : D7) (C : ℝ) (τ : D.what₂.Tau) : (rowEntries D C τ).psiPar =
    (num D C τ).a 0 :: ((List.finRange D.R.m).flatMap (fun i : Fin D.R.m =>
      GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries.block (((num D C τ).cen ((i : ℕ) + 1) : ℤ) : ℚ) (sLen D - 1) ++ [(num D C τ).a ((i : ℕ) + 1)]) ++
      (List.finRange (D.R.k - 1)).map fun i : Fin (D.R.k - 1) => (num D C τ).vHalf ((i : ℕ) + 2)) := rfl

theorem psiPar_props (D : D7) (C : ℝ) (τ : D.what₂.Tau) :
    (rowEntries D C τ).psiPar.Pairwise (· > ·) ∧ ∀ x ∈ (rowEntries D C τ).psiPar, x ∈ (num D C τ).weightX 0 := by
  have hm : (num D C τ).NearMid := num_nearMid D C τ
  have hs : 1 ≤ (num D C τ).s := (odd_sLen D).pos
  have hg : (num D C τ).s < (num D C τ).ga := sLen_lt_gap D C
  have hGm : (num D C τ).m = D.R.m := rfl
  have hGk : (num D C τ).k = D.R.k := rfl
  have hga : (0 : ℚ) < (num D C τ).ga := by exact_mod_cast (by omega : 0 < (num D C τ).ga)
  have hle : ∀ {i j : ℕ}, i ≤ j → (num D C τ).a j ≤ (num D C τ).a i := fun h => by
    rcases h.eq_or_lt with rfl | h
    · exact le_rfl
    · linarith [a_add_le (G := num D C τ) h]
  have hB : ∀ (i : Fin D.R.m) x, x ∈ GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries.block (((num D C τ).cen ((i : ℕ) + 1) : ℤ) : ℚ) (sLen D - 1) →
      (num D C τ).a ((i : ℕ) + 1) < x ∧ x < (num D C τ).a ((i : ℕ) + 1) + (num D C τ).ga := fun i x hx =>
    blockC'_between hm hs hg (by omega) (by have := i.2; omega) (mem_listBlock_iff.1 hx)
  have piece : ∀ (i : Fin D.R.m) y, y ∈ GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries.block (((num D C τ).cen ((i : ℕ) + 1) : ℤ) : ℚ) (sLen D - 1) ++
      [(num D C τ).a ((i : ℕ) + 1)] → (num D C τ).a ((i : ℕ) + 1) ≤ y ∧ y < (num D C τ).a i := by
    intro i y hy
    rw [(num D C τ).a_eq_succ_add i]
    rcases List.mem_append.1 hy with h | h
    · have := hB i y h; exact ⟨this.1.le, this.2⟩
    · rw [List.mem_singleton] at h; subst h
      exact ⟨le_rfl, by linarith⟩
  have hU : ∀ y ∈ (List.finRange (D.R.k - 1)).map (fun i : Fin (D.R.k - 1) => (num D C τ).vHalf ((i : ℕ) + 2)),
      y ∈ (num D C τ).cloudHalf := by
    intro y hy
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hy
    exact GridData.mem_cloudHalf.2 ⟨(i : ℕ) + 2, by omega, by have := i.2; omega, rfl⟩
  rw [psiPar_eq]
  refine ⟨?_, ?_⟩
  · rw [List.pairwise_cons, List.pairwise_append, List.pairwise_flatMap, List.pairwise_map]
    refine ⟨?_, ⟨⟨?_, ?_⟩, ?_, ?_⟩⟩
    · intro y hy
      rcases List.mem_append.1 hy with h | h
      · obtain ⟨i, -, h⟩ := List.mem_flatMap.1 h
        have := piece i y h
        linarith [hle (Nat.zero_le (i : ℕ))]
      · have := cloudHalf_lt (hU y h)
        linarith [hle (Nat.zero_le (num D C τ).m)]
    · intro i _
      rw [List.pairwise_append]
      refine ⟨pairwise_listBlock _ _, List.pairwise_singleton _ _, ?_⟩
      intro x hx y hy
      rw [List.mem_singleton] at hy; subst hy
      exact (hB i x hx).1
    · refine (List.pairwise_lt_finRange D.R.m).imp fun {i j} hij => ?_
      intro x hx y hy
      have h1 := piece i x hx
      have h2 := piece j y hy
      have h3 : (i : ℕ) + 1 ≤ j := hij
      linarith [hle h3]
    · refine (List.pairwise_lt_finRange (D.R.k - 1)).imp fun {i j} hij => ?_
      have hij' : (i : ℕ) < j := hij
      have := (num D C τ).v_anti ((i : ℕ) + 2) ((j : ℕ) + 2) (by omega) (by omega) (by have := j.2; omega)
      have h' : ((num D C τ).v ((j : ℕ) + 2) : ℚ) < (num D C τ).v ((i : ℕ) + 2) := by exact_mod_cast this
      simp only [GridData.vHalf]; linarith
    · intro x hx y hy
      obtain ⟨i, -, h⟩ := List.mem_flatMap.1 hx
      have h1 := piece i x h
      have h2 := cloudHalf_lt (hU y hy)
      have h3 : (i : ℕ) + 1 ≤ (num D C τ).m := by have := i.2; omega
      linarith [hle h3]
  · intro y hy
    rw [GridData.mem_weightX]
    rcases List.mem_cons.1 hy with rfl | hy
    · exact Or.inl (GridData.mem_tops.2 ⟨0, by omega, rfl⟩)
    rcases List.mem_append.1 hy with h | h
    · obtain ⟨i, -, h⟩ := List.mem_flatMap.1 h
      rcases List.mem_append.1 h with h | h
      · exact Or.inr (Or.inr (Or.inl ⟨(i : ℕ) + 1, by omega, by have := i.2; omega, mem_listBlock_iff.1 h⟩))
      · rw [List.mem_singleton] at h; subst h
        exact Or.inl (GridData.mem_tops.2 ⟨(i : ℕ) + 1, by have := i.2; omega, rfl⟩)
    · exact Or.inr (Or.inl (hU y h))

theorem length_psiPar (D : D7) (C : ℝ) (τ : D.what₂.Tau) : (rowEntries D C τ).psiPar.length = rankP D D.R.m := by
  rw [length_psi, rowSizes_nR]; simp [rankX]

end GlobalTheory.RowReal.WeightsX

namespace GlobalTheory.RowReal

open GlobalTheory.SignedHC GlobalTheory.RowReal.WeightsX

end GlobalTheory.RowReal
