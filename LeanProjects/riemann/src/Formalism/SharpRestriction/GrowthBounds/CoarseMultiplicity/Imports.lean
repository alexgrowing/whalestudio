import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.LevOfSymVar

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial

section

variable (C0 CE1 CE2 : ℝ) (X : Loc) [NeZero X.m] (j : Fin (numSeg X.TT))

def ωoL (l0 : Fin (X.seg C0 CE1 CE2 j).t) : Fin (2 * segS X.TT j + 1 + 1) → ℕ :=
  fun a => if (a : ℕ) = 2 * (uTop (X.seg C0 CE1 CE2 j) l0 : ℕ) then 1 else 0

def ωo (l0 : Fin (X.seg C0 CE1 CE2 j).t) : BV C0 CE1 CE2 X j → ℕ
  | Sum.inl (a, _) => ωoL C0 CE1 CE2 X j l0 a
  | Sum.inr (l, β) => if (l : ℕ) = (l0 : ℕ) ∧ β = true then 1 else 0

def ωpL : Fin (2 * segS X.TT j + 1 + 1) → ℕ := fun a => if (a : ℕ) = 2 * segS X.TT j then 1 else 0

def ωp : BV C0 CE1 CE2 X j → ℕ
  | Sum.inl (a, _) => ωpL X j a
  | Sum.inr (l, β) => if (l : ℕ) = (X.seg C0 CE1 CE2 j).t ∧ β = true then 1 else 0

theorem ωo_bal (l0 : Fin (X.seg C0 CE1 CE2 j).t) :
    Balanced X.m (X.seg C0 CE1 CE2 j) (ωo C0 CE1 CE2 X j l0) (ωoL C0 CE1 CE2 X j l0) := by
  refine ⟨fun a c => rfl, fun l => ?_, ?_⟩
  · have hi := (uTop (X.seg C0 CE1 CE2 j) l).2
    have hu : ∀ l' : Fin (X.seg C0 CE1 CE2 j).t, ((uTop (X.seg C0 CE1 CE2 j) l' : Fin _) : ℕ) =
        (X.seg C0 CE1 CE2 j).sigma + l' := fun _ => rfl
    have v0 : ((finPos (2 * segS X.TT j + 1) (2 * (uTop (X.seg C0 CE1 CE2 j) l : ℕ)) : Fin _) : ℕ) =
        2 * (uTop (X.seg C0 CE1 CE2 j) l : ℕ) := Nat.min_eq_left (by omega)
    have v1 : ((finPos (2 * segS X.TT j + 1) (2 * (uTop (X.seg C0 CE1 CE2 j) l : ℕ) + 1) : Fin _) : ℕ) =
        2 * (uTop (X.seg C0 CE1 CE2 j) l : ℕ) + 1 := Nat.min_eq_left (by omega)
    simp only [ωo, ωoL, v0, v1, Fin.val_castSucc]
    by_cases hl : (l : ℕ) = (l0 : ℕ)
    · rw [if_neg (by simp), if_pos (by simp [hl]), if_pos (by rw [hu, hu]; omega), if_neg (by rw [hu, hu]; omega)]
    · rw [if_neg (by simp), if_neg (by simp [hl]), if_neg (by rw [hu, hu]; omega), if_neg (by rw [hu, hu]; omega)]
  · have hi := (uTop (X.seg C0 CE1 CE2 j) l0).2
    simp only [ωo, ωoL, Fin.val_castSucc, Fin.val_last]
    rw [if_neg (by simp), if_neg (by intro h; have := l0.2; omega), if_neg (by omega), if_neg (by omega)]

theorem ωp_bal : Balanced X.m (X.seg C0 CE1 CE2 j) (ωp C0 CE1 CE2 X j) (ωpL X j) := by
  refine ⟨fun a c => rfl, fun l => ?_, ?_⟩
  · have hi := (uTop (X.seg C0 CE1 CE2 j) l).2
    have v0 : ((finPos (2 * segS X.TT j + 1) (2 * (uTop (X.seg C0 CE1 CE2 j) l : ℕ)) : Fin _) : ℕ) =
        2 * (uTop (X.seg C0 CE1 CE2 j) l : ℕ) := Nat.min_eq_left (by omega)
    have v1 : ((finPos (2 * segS X.TT j + 1) (2 * (uTop (X.seg C0 CE1 CE2 j) l : ℕ) + 1) : Fin _) : ℕ) =
        2 * (uTop (X.seg C0 CE1 CE2 j) l : ℕ) + 1 := Nat.min_eq_left (by omega)
    simp only [ωp, ωpL, v0, v1, Fin.val_castSucc]
    rw [if_neg (by simp), if_neg (by intro h; have := l.2; omega), if_neg (by omega), if_neg (by omega)]
  · simp only [ωp, ωpL, Fin.val_castSucc, Fin.val_last]
    simp

theorem omB_ωo (b : SegBlock (segS X.TT j) X.m) (l0 : Fin (X.seg C0 CE1 CE2 j).t) :
    OmB X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (segAPlus X.TT X.aT j) b (ωo C0 CE1 CE2 X j l0)
      (ωoL C0 CE1 CE2 X j l0) = b.o (uTop (X.seg C0 CE1 CE2 j) l0) := by
  classical
  have hi := (uTop (X.seg C0 CE1 CE2 j) l0).2
  unfold OmB
  have s1 : ∑ l : Fin (X.seg C0 CE1 CE2 j).t, (coarseA X.p (X.seg C0 CE1 CE2 j) b (uTop (X.seg C0 CE1 CE2 j) l) -
      b.o (uTop (X.seg C0 CE1 CE2 j) l)) * ωo C0 CE1 CE2 X j l0 (Sum.inr (Fin.castSucc l, false)) = 0 :=
    Finset.sum_eq_zero fun l _ => by simp [ωo]
  have s2 : ωo C0 CE1 CE2 X j l0 (Sum.inr (Fin.last _, false)) = 0 := by simp [ωo]
  have s3 : ∑ a : Fin (2 * segS X.TT j + 1), (segChain X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b).deg a *
      ωoL C0 CE1 CE2 X j l0 (Fin.castSucc a) = b.o (uTop (X.seg C0 CE1 CE2 j) l0) := by
    rw [Finset.sum_eq_single (⟨2 * (uTop (X.seg C0 CE1 CE2 j) l0 : ℕ), by omega⟩ : Fin (2 * segS X.TT j + 1))]
    · simp only [ωoL, Fin.val_castSucc, if_true, mul_one]
      rw [segment_chain_degree_even X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b _ (uTop (X.seg C0 CE1 CE2 j) l0) rfl,
        if_neg (by show ¬ ((X.seg C0 CE1 CE2 j).sigma + (l0 : ℕ) < (X.seg C0 CE1 CE2 j).sigma); omega)]
    · intro a _ ha
      simp only [ωoL, Fin.val_castSucc]
      rw [if_neg (fun h => ha (Fin.ext h)), mul_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
  have s4 : ωoL C0 CE1 CE2 X j l0 (Fin.last _) = 0 := by
    simp only [ωoL, Fin.val_last]
    rw [if_neg (by omega)]
  rw [s1, s2, s3, s4]
  ring

theorem omB_ωp (b : SegBlock (segS X.TT j) X.m) :
    OmB X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (segAPlus X.TT X.aT j) b (ωp C0 CE1 CE2 X j) (ωpL X j) = b.oPlus := by
  classical
  unfold OmB
  have s1 : ∑ l : Fin (X.seg C0 CE1 CE2 j).t, (coarseA X.p (X.seg C0 CE1 CE2 j) b (uTop (X.seg C0 CE1 CE2 j) l) -
      b.o (uTop (X.seg C0 CE1 CE2 j) l)) * ωp C0 CE1 CE2 X j (Sum.inr (Fin.castSucc l, false)) = 0 :=
    Finset.sum_eq_zero fun l _ => by simp [ωp]
  have s2 : ωp C0 CE1 CE2 X j (Sum.inr (Fin.last _, false)) = 0 := by simp [ωp]
  have s3 : ∑ a : Fin (2 * segS X.TT j + 1), (segChain X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b).deg a *
      ωpL X j (Fin.castSucc a) = b.oPlus := by
    rw [Finset.sum_eq_single (⟨2 * segS X.TT j, by omega⟩ : Fin (2 * segS X.TT j + 1))]
    · simp only [ωpL, Fin.val_castSucc, if_true, mul_one]
      exact chain_deg_U X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b _ rfl
    · intro a _ ha
      simp only [ωpL, Fin.val_castSucc]
      rw [if_neg (fun h => ha (Fin.ext h)), mul_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
  have s4 : ωpL X j (Fin.last _) = 0 := by
    simp only [ωpL, Fin.val_last]
    rw [if_neg (by omega)]
  rw [s1, s2, s3, s4]
  ring

end

end Formalism.MainNotions.ColumnSystems.Pf
