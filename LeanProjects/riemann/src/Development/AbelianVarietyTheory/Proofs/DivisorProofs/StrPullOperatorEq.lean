import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TranslationInv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullFullL
open Matrix MeasureTheory Set Filter Topology
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe GlobalTheory.TorsionForm GlobalTheory.TorsionForm.OneVec
open scoped Real ContDiff

set_option autoImplicit false
namespace GlobalTheory.TorsionForm.OneVec.StrPull

theorem mem_join_castAdd {m g : ℕ} (S : Finset (Fin m)) (I : Finset (Fin g)) (i : Fin m) :
    Fin.castAdd g i ∈ join S I ↔ i ∈ S := by
  simp only [join, Finset.mem_union, Finset.mem_map]
  constructor
  · rintro (⟨a, ha, h⟩ | ⟨a, ha, h⟩)
    · have h' := congrArg Fin.val h
      simp at h'
      rwa [← Fin.ext h']
    · have h' := congrArg Fin.val h
      simp at h'
      omega
  · intro h; exact Or.inl ⟨i, h, rfl⟩

theorem mem_join_natAdd {m g : ℕ} (S : Finset (Fin m)) (I : Finset (Fin g)) (c : Fin g) :
    Fin.natAdd m c ∈ join S I ↔ c ∈ I := by
  simp only [join, Finset.mem_union, Finset.mem_map]
  constructor
  · rintro (⟨a, ha, h⟩ | ⟨a, ha, h⟩)
    · have h' := congrArg Fin.val h
      simp at h'
      omega
    · have h' := congrArg Fin.val h
      simp at h'
      rwa [← Fin.ext h']
  · intro h; exact Or.inr ⟨c, h, rfl⟩

theorem basePart_join {m g : ℕ} (S : Finset (Fin m)) (I : Finset (Fin g)) :
    basePart (join S I) = S := by
  ext i; simp [basePart, mem_join_castAdd]

theorem fibrePart_join {m g : ℕ} (S : Finset (Fin m)) (I : Finset (Fin g)) :
    fibrePart (join S I) = I := by
  ext i; simp [fibrePart, mem_join_natAdd]

theorem join_parts {m g : ℕ} (U : Finset (Fin (m + g))) :
    join (basePart U) (fibrePart U) = U := by
  ext x
  refine Fin.addCases (fun i => ?_) (fun c => ?_) x
  · simp [basePart, mem_join_castAdd]
  · simp [fibrePart, mem_join_natAdd]

theorem join_inj {m g : ℕ} {S S' : Finset (Fin m)} {I I' : Finset (Fin g)}
    (h : join S I = join S' I') : S = S' ∧ I = I' := by
  refine ⟨?_, ?_⟩
  · rw [← basePart_join S I, h, basePart_join]
  · rw [← fibrePart_join S I, h, fibrePart_join]

theorem rhoL_single {n g : ℕ} (S' : Finset (Fin (1 + 1))) (I : Finset (Fin g)) :
    rhoL (n := n) S' (Pi.single (join ∅ I) 1) =
      if S' = ∅ then Pi.single (join ∅ I) 1 else 0 := by
  funext U
  change (if basePart U = ∅ then (Pi.single (join ∅ I) 1 : Ext (1 + 1 + g)) (join S' (fibrePart U))
    else 0) = _
  by_cases hS : S' = ∅
  · subst hS
    simp only [if_true, Pi.single_apply]
    by_cases hU : U = join ∅ I
    · subst hU; simp [basePart_join, fibrePart_join]
    · rw [if_neg hU]
      split_ifs with hb hj
      · have hf := (join_inj hj).2
        exact absurd ((join_parts U).symm.trans (by rw [hb, hf])) hU
      · rfl
      · rfl
  · rw [if_neg hS]
    simp only [Pi.single_apply]
    split_ifs with hb hj
    · exact absurd (join_inj hj).1 hS
    · rfl
    · rfl

theorem pullOp_single {n g : ℕ} (a : Fin n → ℂ) (K : Ext (n + n + g) →L[ℂ] Ext (n + n + g))
    (I : Finset (Fin g)) :
    pullOp a K (Pi.single (join ∅ I) 1) = pullFull a (K (Pi.single (join ∅ I) 1)) := by
  rw [pullOp, ContinuousLinearMap.sum_apply, Finset.sum_eq_single (∅ : Finset (Fin (1 + 1)))]
  · simp only [ContinuousLinearMap.comp_apply, rhoL_single, if_true]
    simp [lamL]
    rfl
  · intro S _ hS
    simp [ContinuousLinearMap.comp_apply, rhoL_single, hS]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem pullFull_join {n g : ℕ} (a : Fin n → ℂ) (y : Ext (n + n + g)) (S : Finset (Fin (1 + 1)))
    (I : Finset (Fin g)) :
    pullFull a y (join S I) = pullBase a (fun S' => y (join S' I)) S := by
  simp [pullFull, basePart_join, fibrePart_join]

end GlobalTheory.TorsionForm.OneVec.StrPull

namespace GlobalTheory.TorsionForm.OneVec

open GlobalTheory.TorsionForm.OneVec.StrPull in

theorem strN_pullOp {n g : ℕ} (a : Fin n → ℂ) (K : Ext (n + n + g) →L[ℂ] Ext (n + n + g)) :
    strN (pullOp a K) = pullBaseL a (strN K) := by
  have h : strN K = ∑ I : Finset (Fin g), ((-1) ^ I.card * (I.card : ℂ)) •
      (fun S' : Finset (Fin (n + n)) => K (Pi.single (join ∅ I) 1) (join S' I)) := by
    funext S'
    simp [strN, Finset.sum_apply, smul_eq_mul]
  rw [h, map_sum]
  funext S
  rw [Finset.sum_apply]
  simp only [strN, pullOp_single, pullFull_join, map_smul, Pi.smul_apply, smul_eq_mul]
  rfl

end GlobalTheory.TorsionForm.OneVec
