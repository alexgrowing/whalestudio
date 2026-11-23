import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusThreeBlockApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairInducedEquivProd
open GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.LeviBlockExponent GlobalTheory.IndJacBlock

noncomputable section
namespace GlobalTheory.IndJacBlock.Bwd
open GlobalTheory.SplitFlip GlobalTheory.FullRankCoinv GlobalTheory.FullRankCoinv.IndTwist

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem pairPlace_val_zero {N : ℕ} (b : Fin 2 → ℕ) (h : b 0 + b 1 = N) (j : Fin (b 0)) :
    ((pairPlace b h ⟨0, j⟩ : Fin N) : ℕ) = j := by
  simp [pairPlace]

theorem pairPlace_val_one {N : ℕ} (b : Fin 2 → ℕ) (h : b 0 + b 1 = N) (j : Fin (b 1)) :
    ((pairPlace b h ⟨1, j⟩ : Fin N) : ℕ) = b 0 + j := by
  simp [pairPlace]

theorem lastRows_mul_apply {n d : ℕ} (hnd : n ≤ d) (M : Matrix (Fin d) (Fin d) k) (i : Fin n) (j : Fin d) :
    (FullRankCoinv.Y0 k n d * M) i j = M ⟨d - n + i, by omega⟩ j := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (⟨d - n + i, by omega⟩ : Fin d)]
  · simp [FullRankCoinv.Y0]
  · intro l _ hl
    have : ¬ ((l : ℕ) = d - n + i) := fun h => hl (Fin.ext h)
    simp [FullRankCoinv.Y0, this]
  · simp

theorem mul_lastCols_apply_zero {n d : ℕ} (D : Matrix (Fin n) (Fin n) k) (i : Fin n) (j : Fin d) (hj : (j : ℕ) < d - n) :
    (D * FullRankCoinv.Y0 k n d) i j = 0 := by
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun l _ => ?_
  have : ¬ ((j : ℕ) = d - n + l) := by omega
  simp [FullRankCoinv.Y0, this]

theorem mul_lastCols_apply_last {n d : ℕ} (hnd : n ≤ d) (D : Matrix (Fin n) (Fin n) k) (i l : Fin n) :
    (D * FullRankCoinv.Y0 k n d) i ⟨d - n + l, by omega⟩ = D i l := by
  rw [Matrix.mul_apply, Finset.sum_eq_single l]
  · simp [FullRankCoinv.Y0]
  · intro l' _ hl
    have : ¬ (d - n + (l : ℕ) = d - n + l') := fun h => hl (Fin.ext (by omega))
    simp only [FullRankCoinv.Y0, Matrix.of_apply, if_neg this, mul_zero]
  · simp

theorem mem_parabolic_of_lastRows_intertwine {n d : ℕ} (hnd : n ≤ d) {b : GL (Fin d) k} {D : GL (Fin n) k}
    (hD : FullRankCoinv.Y0 k n d * b.1 = D.1 * FullRankCoinv.Y0 k n d) :
    b ∈ parab k (pairPlace (b2 n d) (block_size_pair_sum hnd)) := by
  rw [mem_parab_iff]
  intro a c i j hca
  fin_cases a <;> fin_cases c
  · exact absurd hca (by decide)
  · exact absurd hca (by decide)
  · have hj : ((pairPlace (b2 n d) (block_size_pair_sum hnd) ⟨0, j⟩ : Fin d) : ℕ) < d - n := by
      rw [pairPlace_val_zero]; exact j.2
    have h := congrFun (congrFun hD (show Fin n from i)) (pairPlace (b2 n d) (block_size_pair_sum hnd) ⟨0, j⟩)
    rw [lastRows_mul_apply hnd, mul_lastCols_apply_zero _ _ _ hj] at h
    rw [← h]
    exact congrArg (fun l => b.1 l _) (Fin.ext (pairPlace_val_one (b2 n d) (block_size_pair_sum hnd) i))
  · exact absurd hca (by decide)

theorem leviProj_eq_of_lastRows_intertwine {n d : ℕ} (hnd : n ≤ d) (b : parab k (pairPlace (b2 n d) (block_size_pair_sum hnd)))
    {D : GL (Fin n) k} (hD : FullRankCoinv.Y0 k n d * (b : GL (Fin d) k).1 = D.1 * FullRankCoinv.Y0 k n d) :
    (show GL (Fin n) k from leviProj k _ b 1) = D := by
  ext i j
  have h := congrFun (congrFun hD i) ⟨d - n + j, by omega⟩
  rw [lastRows_mul_apply hnd, mul_lastCols_apply_last hnd] at h
  rw [← h]
  refine (leviProj_apply k _ b 1 i j).trans ?_
  exact congrArg₂ (b : GL (Fin d) k).1 (Fin.ext (pairPlace_val_one (b2 n d) (block_size_pair_sum hnd) i))
    (Fin.ext (pairPlace_val_one (b2 n d) (block_size_pair_sum hnd) j))

theorem bwd : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n d : ℕ) (hnd : n ≤ d) (ν : kˣ →* ℂˣ)
    (F : IndSp (pairPlace (b2 n d) (block_size_pair_sum hnd)) (ofChar (pairChar k (b2 n d) (chi2 k ν)))),
    GlobalTheory.FullRankCoinv.IndTwist.detTw d (-((n : ℂ) / 2)) F.1.1 ∈ GlobalTheory.FullRankCoinv.indSp k n d ν := by
  intro k _ _ _ _ n d hnd ν F
  have hK : IsSmoothChar (detChar (Fin d) (absPow k (-((n : ℂ) / 2)))) :=
    (isSmoothChar_of_isUnram (isUnram_absPow k _)).detChar
  have hK1 : ((detChar (Fin d) (absPow k (-((n : ℂ) / 2)))).ker : Set (GL (Fin d) k)) ∈ nhds 1 :=
    hK.mem_nhds (by simp)
  have hU := IsOpen.mem_nhds (x := (1 : GL (Fin d) k)) F.2 (by simp)
  refine ⟨⟨_, Filter.inter_mem hU hK1, fun h u hu => ?_⟩, fun b h D hD => ?_⟩
  · have hg2 : apow (gdet u) (-((n : ℂ) / 2)) = 1 := by
      have := congrArg Units.val (MonoidHom.mem_ker.1 hu.2)
      exact this
    have hFu : F.1.1 (h * u) = F.1.1 h := by
      have hg' := hu.1
      exact congrFun (congrArg Subtype.val hg') h
    simp only [detTw_apply, gdet_mul, apow_mul, hg2, mul_one, hFu]
  · let p : parab k (pairPlace (b2 n d) (block_size_pair_sum hnd)) := ⟨b, mem_parabolic_of_lastRows_intertwine hnd hD⟩
    have hp : Matrix.GeneralLinearGroup.det (leviProj k _ p 1) = gdet D :=
      congrArg gdet (leviProj_eq_of_lastRows_intertwine hnd p hD)
    have hlaw := parInd_law _ _ F p h
    have hdet : gdet b = Matrix.GeneralLinearGroup.det (leviProj k _ p 0) * gdet D := by
      have := det_parab k _ p
      rw [Fin.prod_univ_two, hp] at this
      exact this
    rw [GlobalTheory.PairIndProd.deltaHalf_pair, ofChar_apply, GlobalTheory.PairIndProd.pairChar_apply', hp] at hlaw
    generalize Matrix.GeneralLinearGroup.det (leviProj k _ p 0) = A at hlaw hdet
    have hlaw' : F.1.1 (b * h) = apow A ((n : ℂ) / 2) * apow (gdet D) (-((d - n : ℕ) : ℂ) / 2) *
        ((((ν (gdet D))⁻¹ : ℂˣ) : ℂ) * F.1.1 h) := by
      refine hlaw.trans ?_
      have e0 : chi2 k ν 0 A = 1 := rfl
      have e1 : chi2 k ν 1 (gdet D) = (ν (gdet D))⁻¹ := rfl
      rw [e0, e1, one_mul]
      rfl
    have e2 : apow A (-((n : ℂ) / 2)) * apow A ((n : ℂ) / 2) = 1 := by
      rw [← apow_add]; simp
    have e3 : apow (gdet D) (-(d : ℂ) / 2) =
        apow (gdet D) (-((n : ℂ) / 2)) * apow (gdet D) (-((d - n : ℕ) : ℂ) / 2) := by
      rw [← apow_add, Nat.cast_sub hnd]; congr 1; ring
    simp only [detTw_apply, gdet_mul, apow_mul, hlaw', hdet, e3]
    linear_combination (apow (gdet D) (-((n : ℂ) / 2)) * apow (gdet h) (-((n : ℂ) / 2)) *
      apow (gdet D) (-((d - n : ℕ) : ℂ) / 2) * (((ν (gdet D))⁻¹ : ℂˣ) : ℂ) * F.1.1 h) * e2

end GlobalTheory.IndJacBlock.Bwd
