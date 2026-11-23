import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LoopTerm
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.OfRoots
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RatCoordCont
open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf Formalism.L2.SG.LoopTieOf
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RootsBijection

open Formalism.L2.SG.RealObj in
theorem fwd {K : Type*} [Zero K] : ∀ (bs : List (K × ℕ)) (i j a b : ℕ), Formalism.MainNotions.S.ptEntry bs i a ≠ 0 →
    Formalism.MainNotions.S.ptEntry bs j b ≠ 0 → a < b → j < i → blkOf bs a = blkOf bs b
  | [], _, _, _, _, h, _, _, _ => by simp [Formalism.MainNotions.S.ptEntry] at h
  | (t, s) :: bs, i, j, a, b, h1, h2, hab, hji => by
    rw [Formalism.MainNotions.S.ptEntry] at h1 h2
    by_cases ha : a < s
    · by_cases hb : b < s
      · simp [blkOf, ha, hb]
      · exfalso
        rw [if_neg (show ¬ (j < s ∧ b < s) by omega)] at h2
        by_cases hj : s ≤ j
        · rw [if_neg (show ¬ (s ≤ i ∧ s ≤ a) by omega)] at h1
          by_cases hi : i < s
          · omega
          · rw [if_neg (show ¬ (i < s ∧ a < s) by omega)] at h1; exact h1 rfl
        · rw [if_neg (show ¬ (s ≤ j ∧ s ≤ b) by omega)] at h2; exact h2 rfl
    · have hb : ¬ b < s := by omega
      rw [if_neg (show ¬ (i < s ∧ a < s) by omega)] at h1
      rw [if_neg (show ¬ (j < s ∧ b < s) by omega)] at h2
      by_cases hi : s ≤ i
      · by_cases hj : s ≤ j
        · rw [if_pos ⟨hi, by omega⟩] at h1
          rw [if_pos ⟨hj, by omega⟩] at h2
          have := fwd bs (i - s) (j - s) (a - s) (b - s) h1 h2 (by omega) (by omega)
          simp [blkOf, ha, hb, this]
        · rw [if_neg (show ¬ (s ≤ j ∧ s ≤ b) by omega)] at h2; exact absurd rfl h2
      · rw [if_neg (show ¬ (s ≤ i ∧ s ≤ a) by omega)] at h1; exact absurd rfl h1

open Formalism.L2.SG.RealObj in
theorem bwd {K : Type*} [Zero K] : ∀ (bs : List (K × ℕ)), (∀ p ∈ bs, p.1 ≠ 0) → ∀ (a b : ℕ), a < b →
    b < (bs.map Prod.snd).sum → blkOf bs a = blkOf bs b →
    ∃ i j, j < i ∧ i < (bs.map Prod.snd).sum ∧ Formalism.MainNotions.S.ptEntry bs i a ≠ 0 ∧ Formalism.MainNotions.S.ptEntry bs j b ≠ 0
  | [], _, _, _, _, hb, _ => by simp at hb
  | (t, s) :: bs, hnz, a, b, hab, hbs, hbl => by
    have ht : t ≠ 0 := hnz (t, s) (by simp)
    simp only [List.map_cons, List.sum_cons] at hbs ⊢
    by_cases ha : a < s
    · have hb : b < s := by
        by_contra hb
        simp [blkOf, ha, hb] at hbl
      refine ⟨s - 1 - a, s - 1 - b, by omega, by omega, ?_, ?_⟩
      · rw [Formalism.MainNotions.S.ptEntry, if_pos ⟨by omega, ha⟩, if_pos (by omega)]; exact ht
      · rw [Formalism.MainNotions.S.ptEntry, if_pos ⟨by omega, hb⟩, if_pos (by omega)]; exact ht
    · have hb : ¬ b < s := by omega
      have hbl' : blkOf bs (a - s) = blkOf bs (b - s) := by
        simpa [blkOf, ha, hb] using hbl
      obtain ⟨i, j, hji, his, hi, hj⟩ := bwd bs (fun p hp => hnz p (by simp [hp])) (a - s) (b - s) (by omega)
        (by omega) hbl'
      refine ⟨i + s, j + s, by omega, by omega, ?_, ?_⟩
      · rw [Formalism.MainNotions.S.ptEntry, if_neg (by omega), if_pos ⟨by omega, by omega⟩]; simpa using hi
      · rw [Formalism.MainNotions.S.ptEntry, if_neg (by omega), if_pos ⟨by omega, by omega⟩]; simpa using hj

end GlobalTheory.RootsBijection

theorem GlobalTheory.roots_ptMat_iff : ∀ (K : Type) [Field K] (n : ℕ) (w : Point K n) (a b : Fin n),
    (a, b) ∈ GlobalTheory.LoopV.roots (ptMat w) ↔ a < b ∧ Formalism.L2.SG.RealObj.blkOf w.1 a.1 = Formalism.L2.SG.RealObj.blkOf w.1 b.1 := by
  intro K _ n w a b
  unfold GlobalTheory.LoopV.roots
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  simp only [ptMat]
  constructor
  · rintro ⟨hab, i, j, hji, hi, hj⟩
    exact ⟨hab, GlobalTheory.RootsBijection.fwd w.1 i.1 j.1 a.1 b.1 hi hj hab hji⟩
  · rintro ⟨hab, hbl⟩
    obtain ⟨i, j, hji, hin, hi, hj⟩ := GlobalTheory.RootsBijection.bwd w.1 (fun p hp => (w.2.1 p hp).1) a.1 b.1 hab
      (by rw [w.2.2]; exact b.2) hbl
    rw [w.2.2] at hin
    exact ⟨hab, ⟨i, hin⟩, ⟨j, by omega⟩, hji, hi, hj⟩
