import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.LeadingExponentHomogeneous
import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.FTDefs

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial

section

variable (C0 CE1 CE2 : ℝ) (X : Loc) [NeZero X.m] (j : Fin (numSeg X.TT))

theorem lev_of_symVar (v : BV C0 CE1 CE2 X j) (i : Fin (segS X.TT j)) (h : (symVar C0 CE1 CE2 X j v).1.1 = topOdd X j i) :
    symLev X.p C0 CE1 CE2 X j v = (X.seg C0 CE1 CE2 j).P X.p i := by
  rcases v with ⟨a, c⟩ | ⟨l, bo⟩
  · by_cases ha : (a : ℕ) < 2 * segS X.TT j
    · simp only [symVar, symLev, dif_pos ha] at h ⊢
      rw [topOdd_inj X j h]
    · simp only [symVar, dif_neg ha] at h
      exact absurd h.symm (topOdd_ne_end X j i)
  · by_cases hl : (l : ℕ) < (X.seg C0 CE1 CE2 j).t
    · simp only [symVar, symLev, dif_pos hl] at h ⊢
      rw [topOdd_inj X j h]
    · simp only [symVar, dif_neg hl] at h
      exact absurd h.symm (topOdd_ne_end X j i)

theorem coarse_dvd (μ : BV C0 CE1 CE2 X j →₀ ℕ) (i : Fin (segS X.TT j)) (β : Bool) (c : Fin (X.m + 1)) :
    (X.seg C0 CE1 CE2 j).P X.p i ∣
      (μ.sum fun v n => Finsupp.single (symVar C0 CE1 CE2 X j v) (symLev X.p C0 CE1 CE2 X j v * n)) ((topOdd X j i, β), c) := by
  classical
  rw [Finsupp.sum_apply]
  refine Finset.dvd_sum fun v _ => ?_
  show _ ∣ (Finsupp.single (symVar C0 CE1 CE2 X j v) (symLev X.p C0 CE1 CE2 X j v * μ v)) ((topOdd X j i, β), c)
  rw [Finsupp.single_apply]
  split_ifs with h
  · rw [lev_of_symVar C0 CE1 CE2 X j v i (by rw [h])]
    exact dvd_mul_right _ _
  · exact dvd_zero _

theorem coarse_spec (μ : BV C0 CE1 CE2 X j →₀ ℕ) (i : Fin (segS X.TT j)) (β : Bool)
    (hi : (i : ℕ) < (X.seg C0 CE1 CE2 j).sigma) :
    (μ.sum fun v n => Finsupp.single (symVar C0 CE1 CE2 X j v) (symLev X.p C0 CE1 CE2 X j v * n))
      ((topOdd X j i, β), 0) = 0 := by
  classical
  rw [Finsupp.sum_apply]
  refine Finset.sum_eq_zero fun v _ => ?_
  show (Finsupp.single (symVar C0 CE1 CE2 X j v) (symLev X.p C0 CE1 CE2 X j v * μ v)) ((topOdd X j i, β), 0) = 0
  rw [Finsupp.single_apply, if_neg]
  intro h
  rcases v with ⟨a, c⟩ | ⟨l, bo⟩
  · simp only [symVar] at h
    split_ifs at h <;> exact Fin.succ_ne_zero _ (congrArg Prod.snd h)
  · simp only [symVar] at h
    split_ifs at h with hl
    · have e := topOdd_inj X j (congrArg (fun z => z.1.1) h)
      have : (X.seg C0 CE1 CE2 j).sigma + (l : ℕ) = (i : ℕ) := congrArg Fin.val e
      omega
    · exact topOdd_ne_end X j i (congrArg (fun z => z.1.1) h).symm

theorem ioExp_mod (b : SegBlock (segS X.TT j) X.m)
    (hb : Kept X.p X.m (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b) (μ : BV C0 CE1 CE2 X j →₀ ℕ)
    (i : Fin (segS X.TT j)) (β : Bool) (c : Fin (X.m + 1)) :
    ioExp C0 CE1 CE2 X j b μ ((topOdd X j i, β), c) % (X.seg C0 CE1 CE2 j).P X.p i =
      if β then b.rz i c else b.ry i c := by
  unfold ioExp
  rw [Finsupp.add_apply, baseExp_odd]
  obtain ⟨k, hk⟩ := coarse_dvd C0 CE1 CE2 X j μ i β c
  rw [hk]
  have hlt : (if β then b.rz i c else b.ry i c) < (X.seg C0 CE1 CE2 j).P X.p i := by
    split_ifs
    · exact (hb.1.1 i c).1
    · exact (hb.1.1 i c).2
  set P := (X.seg C0 CE1 CE2 j).P X.p i
  have e1 : ∀ (cond : Prop) [Decidable cond] (T : ℕ), (if cond then P * T else 0) = P * (if cond then T else 0) := by
    intro cond _ T
    split_ifs <;> simp
  rw [e1, add_assoc, ← mul_add, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]

end

end Formalism.MainNotions.ColumnSystems.Pf
