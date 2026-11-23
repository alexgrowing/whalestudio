import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.LeibnizDerivatives.GenericProdIff
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OpenFns
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir.Leib GlobalTheory.CompanionTheory.Rodier
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.Rodier

theorem antitone_comp_of_adjacent {h N : ℕ} (b : Fin N → Fin h) (w : Equiv.Perm (Fin N))
    (hstep : ∀ i j : Fin N, (j : ℕ) = i + 1 → b (w j) ≤ b (w i)) :
    Antitone (b ∘ w) := by
  intro x y hxy
  obtain ⟨x, hx⟩ := x
  obtain ⟨y, hy⟩ := y
  simp only [Fin.mk_le_mk] at hxy
  revert hy
  induction y, hxy using Nat.le_induction with
  | base => intro hy; exact le_rfl
  | succ n hxn ih =>
    intro hy
    have hn : n < N := by omega
    exact le_trans (hstep ⟨n, hn⟩ ⟨n + 1, hy⟩ rfl) (ih hn)

theorem blk_comp_wOpen_antitone {h N : ℕ} (d : Fin h → ℕ) (hd : ∑ a, d a = N) :
    Antitone (blk (stdBlocks d hd) ∘ wOpen d hd) := by
  intro x y hxy
  have hm := Tuple.monotone_sort (wKey d hd) hxy
  simp only [Function.comp, wKey] at hm
  rcases Prod.Lex.toLex_le_toLex.mp hm with h | ⟨h, -⟩
  · exact (OrderDual.toDual_lt_toDual.mp h).le
  · exact le_of_eq (OrderDual.toDual_inj.mp h).symm

theorem pm_mem_parab_of_blk_eq (k : Type) [Field k] {h N : ℕ} (d : Fin h → ℕ) (hd : ∑ a, d a = N)
    (v : Equiv.Perm (Fin N)) (hv : ∀ q, blk (stdBlocks d hd) (v q) = blk (stdBlocks d hd) q) :
    pm k v ∈ parab k (stdBlocks d hd) := by
  show (↑(pm k v) : Matrix (Fin N) (Fin N) k).BlockTriangular (blk (stdBlocks d hd))
  intro i j hij
  have hne : v⁻¹ i ≠ j := by
    intro hj
    subst hj
    have hb := hv (v⁻¹ i)
    have hvi : v (v⁻¹ i) = i := by simp
    rw [hvi] at hb
    rw [← hb] at hij
    exact lt_irrefl _ hij
  change (Equiv.toPEquiv v⁻¹).toMatrix i j = 0
  rw [PEquiv.toMatrix_apply]
  simpa using hne

theorem cell_eq_of_blk_eq (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {h N : ℕ} (d : Fin h → ℕ) (hd : ∑ a, d a = N)
    (w w' : Equiv.Perm (Fin N))
    (hw : ∀ p, blk (stdBlocks d hd) (w p) = blk (stdBlocks d hd) (w' p)) :
    cell k d hd w = cell k d hd w' := by
  have key : ∀ u u' : Equiv.Perm (Fin N),
      (∀ p, blk (stdBlocks d hd) (u p) = blk (stdBlocks d hd) (u' p)) → cell k d hd u ⊆ cell k d hd u' := by
    intro u u' hu g hg
    simp only [cell, Set.mem_ofPred_eq] at hg ⊢
    obtain ⟨p, hp, n, hn, rfl⟩ := hg
    have hv : ∀ q, blk (stdBlocks d hd) ((u * u'⁻¹) q) = blk (stdBlocks d hd) q := by
      intro q
      rw [Equiv.Perm.mul_apply, hu]
      simp
    have hpm : pm k u = pm k (u * u'⁻¹) * pm k u' := by
      unfold pm
      rw [← map_mul, inv_mul_cancel_right]
    refine ⟨p * pm k (u * u'⁻¹), (parab k (stdBlocks d hd)).mul_mem hp (pm_mem_parab_of_blk_eq k d hd _ hv),
      n, hn, ?_⟩
    rw [hpm]
    simp only [mul_assoc]
  exact Set.Subset.antisymm (key w w' hw) (key w' w fun p => (hw p).symm)

theorem exists_adjacent_blk_lt_or_cell_eq_open : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (h N : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N) (w : Equiv.Perm (Fin N)),
    (∃ i j : Fin N, (j : ℕ) = i + 1 ∧ blk (stdBlocks d hd) (w i) < blk (stdBlocks d hd) (w j)) ∨
      cell k d hd w = cell k d hd (wOpen d hd) := by
  intro k _ _ _ _ h N d hd w
  by_cases hex : ∃ i j : Fin N, (j : ℕ) = i + 1 ∧ blk (stdBlocks d hd) (w i) < blk (stdBlocks d hd) (w j)
  · exact Or.inl hex
  · right
    simp only [not_exists, not_and, not_lt] at hex
    have hA := antitone_comp_of_adjacent (blk (stdBlocks d hd)) w hex
    have hB := blk_comp_wOpen_antitone d hd
    have hU := Tuple.unique_monotone (f := fun q => OrderDual.toDual (blk (stdBlocks d hd) q))
      (σ := w) (τ := wOpen d hd) (monotone_toDual_comp_iff.mpr hA) (monotone_toDual_comp_iff.mpr hB)
    refine cell_eq_of_blk_eq k d hd w (wOpen d hd) fun p => ?_
    exact OrderDual.toDual_inj.mp (congrFun hU p)

end GlobalTheory.CompanionTheory.Rodier
