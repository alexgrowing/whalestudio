import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.LeibnizDerivatives.GenericProdIff
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OpenFns
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir.Leib GlobalTheory.CompanionTheory.Rodier
open scoped TensorProduct

noncomputable section

open GroundTheory.Automorphic GroundTheory.Automorphic.Iwasawa GroundTheory.Automorphic.Parabolic DoubleCoset

namespace GlobalTheory.CompanionTheory.Rodier.CellOrder

def blkNat {h N : ℕ} (d : Fin h → ℕ) (hd : ∑ a, d a = N) (i : Fin N) : ℕ :=
  ((blk (stdBlocks d hd) i : Fin h) : ℕ)

def idxNat {N : ℕ} (i : Fin N) : ℕ := i

theorem card_filter_le_of_antitone {N : ℕ} (β : Fin N → ℕ) (u w : Equiv.Perm (Fin N))
    (hu : Antitone (β ∘ u)) (a b : ℕ) :
    (Finset.univ.filter fun j : Fin N => (j : ℕ) ≤ b ∧ a ≤ β (w j)).card ≤
      (Finset.univ.filter fun j : Fin N => (j : ℕ) ≤ b ∧ a ≤ β (u j)).card := by
  classical
  by_cases hsub : ∀ j : Fin N, (j : ℕ) ≤ b → a ≤ β (u j)
  · apply Finset.card_le_card
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
    exact ⟨hj.1, hsub j hj.1⟩
  · push Not at hsub
    obtain ⟨i, hib, hia⟩ := hsub
    have hdown : ∀ j : Fin N, a ≤ β (u j) → (j : ℕ) ≤ b := by
      intro j hj
      by_contra hjb
      push Not at hjb
      have hij : i ≤ j := by
        rw [Fin.le_iff_val_le_val]
        omega
      exact absurd (le_trans hj (hu hij)) (not_le.2 hia)
    have e1 : (Finset.univ.filter fun j : Fin N => (j : ℕ) ≤ b ∧ a ≤ β (u j)) =
        Finset.univ.filter fun j : Fin N => a ≤ β (u j) := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨fun h => h.2, fun h => ⟨hdown j h, h⟩⟩
    rw [e1]
    calc (Finset.univ.filter fun j : Fin N => (j : ℕ) ≤ b ∧ a ≤ β (w j)).card
        ≤ (Finset.univ.filter fun j : Fin N => a ≤ β (w j)).card := by
          apply Finset.card_le_card
          intro j hj
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
          exact hj.2
      _ = (Finset.univ.filter fun j : Fin N => a ≤ β (u j)).card := by
          apply Finset.card_bij' (fun j _ => u.symm (w j)) (fun j _ => w.symm (u j)) <;> simp_all

theorem exists_diag_mul_unip {k : Type} [Field k] {N : ℕ} (b : GL (Fin N) k)
    (hb : b ∈ blockUpper k N (idxNat (N := N))) :
    ∃ t : GL (Fin N) k, (∀ i j, i ≠ j → (t : Matrix (Fin N) (Fin N) k) i j = 0) ∧
      ∃ n ∈ unipB k (Fin N), b = t * n := by
  classical
  have hb' : (b : Matrix (Fin N) (Fin N) k).BlockTriangular id := fun i j h => hb h
  have hdet : ∏ i, (b : Matrix (Fin N) (Fin N) k) i i ≠ 0 := by
    rw [← Matrix.det_of_upperTriangular hb']
    exact (Matrix.isUnits_det_units b).ne_zero
  have hD : ∀ i, (b : Matrix (Fin N) (Fin N) k) i i ≠ 0 :=
    fun i => (Finset.prod_ne_zero_iff.1 hdet) i (Finset.mem_univ i)
  let D : Fin N → k := fun i => (b : Matrix (Fin N) (Fin N) k) i i
  let t : GL (Fin N) k := ⟨Matrix.diagonal D, Matrix.diagonal D⁻¹, by
      rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
      congr 1
      funext i
      exact mul_inv_cancel₀ (hD i), by
      rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
      congr 1
      funext i
      exact inv_mul_cancel₀ (hD i)⟩
  refine ⟨t, fun i j hij => Matrix.diagonal_apply_ne _ hij, t⁻¹ * b, ?_, (mul_inv_cancel_left t b).symm⟩
  have hval : ((t⁻¹ * b : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) =
      Matrix.diagonal D⁻¹ * (b : Matrix (Fin N) (Fin N) k) := rfl
  have hP : ((t⁻¹ * b : GL (Fin N) k) : Matrix (Fin N) (Fin N) k).BlockTriangular
      (GlobalTheory.SmGL.blk (GlobalTheory.SmGL.points (Fin N))) := by
    rw [hval]
    exact (Matrix.blockTriangular_diagonal _).mul (fun i j h => hb h)
  show t⁻¹ * b ∈ GlobalTheory.SmGL.unipRad k (GlobalTheory.SmGL.points (Fin N))
  unfold GlobalTheory.SmGL.unipRad
  rw [Subgroup.mem_map]
  refine ⟨⟨t⁻¹ * b, hP⟩, ?_, rfl⟩
  rw [MonoidHom.mem_ker]
  funext a
  apply Units.ext
  ext x y
  change ((t⁻¹ * b : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) a a = (1 : Matrix Unit Unit k) x y
  rw [hval, Matrix.diagonal_mul, Subsingleton.elim x y, Matrix.one_apply_eq]
  exact inv_mul_cancel₀ (hD a)

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {h N : ℕ} (d : Fin h → ℕ) (hd : ∑ a, d a = N)

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in

theorem parab_eq_blockUpper :
    parab k (stdBlocks d hd) = blockUpper k N (blkNat d hd) := by
  ext g
  exact Iff.rfl

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in

theorem unipB_le_blockUpper : unipB k (Fin N) ≤ blockUpper k N (idxNat (N := N)) := by
  intro g hg
  obtain ⟨p, -, rfl⟩ := Subgroup.mem_map.1 hg
  exact fun i j h => p.2 h

theorem cell_eq_doubleCoset (w : Equiv.Perm (Fin N)) :
    cell k d hd w = doubleCoset (pm k w) (blockUpper k N (blkNat d hd) : Set (GL (Fin N) k))
      (blockUpper k N (idxNat (N := N))) := by
  ext g
  rw [DoubleCoset.mem_doubleCoset]
  constructor
  · rintro ⟨p, hp, n, hn, rfl⟩
    rw [parab_eq_blockUpper] at hp
    exact ⟨p, hp, n, unipB_le_blockUpper k hn, rfl⟩
  · rintro ⟨p, hp, q, hq, rfl⟩
    obtain ⟨t, ht, n, hn, rfl⟩ := exists_diag_mul_unip q hq
    refine ⟨p * (pm k w * t * (pm k w)⁻¹), ?_, n, hn, by group⟩
    rw [parab_eq_blockUpper]
    refine Subgroup.mul_mem _ hp ?_
    unfold pm
    rw [GroundTheory.Automorphic.Parabolic.conj_permGL_mem_blockUpper_iff]
    intro i j hij
    exact ht i j (fun h => by subst h; exact lt_irrefl _ hij)

theorem antitone_blkNat_wOpen : Antitone (blkNat d hd ∘ wOpen d hd) := by
  intro i j hij
  have hm := Tuple.monotone_sort (wKey d hd) hij
  simp only [Function.comp_apply] at hm ⊢
  unfold wOpen blkNat
  unfold wKey at hm
  rcases (Prod.Lex.toLex_le_toLex).1 hm with h1 | ⟨h1, -⟩
  · exact (Fin.lt_def.1 (OrderDual.toDual_lt_toDual.1 h1)).le
  · exact le_of_eq (congrArg Fin.val (OrderDual.toDual_inj.1 h1)).symm

theorem cellRank_le_wOpen (w : Equiv.Perm (Fin N)) (a b : ℕ) :
    cellRank (blkNat d hd) idxNat (pm k w) a b ≤
      cellRank (blkNat d hd) idxNat (pm k (wOpen d hd)) a b := by
  unfold pm
  rw [GroundTheory.Automorphic.Parabolic.cellRank_permGL, GroundTheory.Automorphic.Parabolic.cellRank_permGL]
  exact card_filter_le_of_antitone (blkNat d hd) (wOpen d hd) w (antitone_blkNat_wOpen d hd) a b

theorem cells_cover_height :
    (∀ g : GL (Fin N) k, ∃ w, g ∈ cell k d hd w) ∧ ∃ ht : GL (Fin N) k → ℕ,
      (∀ w, ∀ g ∈ cell k d hd w, ht g = ht (pm k w)) ∧
      (∀ w, closure (cell k d hd w) ⊆ cell k d hd w ∪ {x | ht x < ht (pm k w)}) ∧
      ∀ w, cell k d hd w ≠ cell k d hd (wOpen d hd) → ht (pm k w) < ht (pm k (wOpen d hd)) := by
  refine ⟨fun g => ?_, GroundTheory.Automorphic.Parabolic.cellHeight (blkNat d hd) idxNat, fun w g hg => ?_,
    fun w => ?_, fun w hw => ?_⟩
  · obtain ⟨w, hw⟩ := GroundTheory.Automorphic.Parabolic.exists_permGL_mem_doubleCoset
      (F := k) (β := blkNat d hd) (γ := idxNat) g
    refine ⟨w, ?_⟩
    rw [cell_eq_doubleCoset]
    exact hw
  · rw [cell_eq_doubleCoset] at hg
    exact GroundTheory.Automorphic.Parabolic.cellHeight_of_mem_doubleCoset hg
  · rw [cell_eq_doubleCoset]
    exact GroundTheory.Automorphic.Parabolic.closure_doubleCoset_subset _
  · by_contra hle
    push Not at hle
    have hr := GroundTheory.Automorphic.Parabolic.cellRank_eq_of_le_of_cellHeight_le
      (fun a b => cellRank_le_wOpen k d hd w a b) hle
    have hmem := GroundTheory.Automorphic.Parabolic.mem_doubleCoset_of_cellRank_eq hr
    apply hw
    rw [cell_eq_doubleCoset, cell_eq_doubleCoset, DoubleCoset.doubleCoset_eq_of_mem hmem]

theorem cells_main : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (h N : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N), (∀ g : GL (Fin N) k, ∃ w, g ∈ cell k d hd w) ∧ ∃ ht : GL (Fin N) k → ℕ, (∀ w, ∀ g ∈ cell k d hd w, ht g = ht (pm k w)) ∧ (∀ w, closure (cell k d hd w) ⊆ cell k d hd w ∪ {x | ht x < ht (pm k w)}) ∧ ∀ w, cell k d hd w ≠ cell k d hd (wOpen d hd) → ht (pm k w) < ht (pm k (wOpen d hd)) := by
  intro k _ _ _ _ h N d hd
  exact cells_cover_height k d hd

end GlobalTheory.CompanionTheory.Rodier.CellOrder
