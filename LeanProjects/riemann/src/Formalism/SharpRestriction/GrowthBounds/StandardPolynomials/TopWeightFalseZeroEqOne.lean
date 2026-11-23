import Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.IoDVariableLastEqTopEnd

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial

section

variable {C0 CE1 CE2 mu : ℝ} {X : Loc} [NeZero X.m] {β : GlobalTheory X}

def tgHD (L : LvDat C0 CE1 CE2 mu X β) (j : Fin (numSeg X.TT)) (ju : Fin (X.seg C0 CE1 CE2 j).t → ℕ)
    (du : Fin (2 * segS X.TT j + 1) → ℕ) (ω : (X.TT × Bool) × Fin (X.m + 1) → ℕ) : ℕ :=
  (∑ i : Fin (segS X.TT j), (X.seg C0 CE1 CE2 j).P X.p i *
    ((jE (X.seg C0 CE1 CE2 j) ju i.val + du (chW i)) * ω ((topOdd X j i, true), Fin.succ 0) +
      (jE (X.seg C0 CE1 CE2 j) ju i.val + du (chE i)) * ω ((topOdd X j i, false), Fin.succ 0))) +
  (L.jp j * (ω ((topEnd X j, true), Fin.succ 0) + ω ((topEnd X j, false), Fin.succ 0)) +
    du (chU _) * ω ((topEnd X j, true), Fin.succ 0))

def tgWM (X : Loc) (j : Fin (numSeg X.TT)) (A : MonH X) (ω : (X.TT × Bool) × Fin (X.m + 1) → ℕ) : ℕ :=
  (∑ i : Fin (segS X.TT j), ∑ c : Fin (X.m + 1),
    (A ((topOdd X j i, true), c) * ω ((topOdd X j i, true), c) + A ((topOdd X j i, false), c) * ω ((topOdd X j i, false), c))) +
  ∑ c : Fin (X.m + 1), (A ((topEnd X j, true), c) * ω ((topEnd X j, true), c) +
    A ((topEnd X j, false), c) * ω ((topEnd X j, false), c))

variable (O : Type) [CommRing O] [IsDomain O]

theorem tg_segMon_wh (j : Fin (numSeg X.TT)) (A : MonH X) (ω : (X.TT × Bool) × Fin (X.m + 1) → ℕ) :
    IsWeightedHomogeneous ω (segMon O X j A) (tgWM X j A ω) := by
  have h1 : IsWeightedHomogeneous ω (∏ i : Fin (segS X.TT j), ∏ c : Fin (X.m + 1),
      ((MvPolynomial.X ((topOdd X j i, true), c) : RHH O X) ^ A ((topOdd X j i, true), c) *
        MvPolynomial.X ((topOdd X j i, false), c) ^ A ((topOdd X j i, false), c)))
      (∑ i : Fin (segS X.TT j), ∑ c : Fin (X.m + 1),
        (A ((topOdd X j i, true), c) • ω ((topOdd X j i, true), c) +
          A ((topOdd X j i, false), c) • ω ((topOdd X j i, false), c))) :=
    IsWeightedHomogeneous.prod _ _ _ (fun i _ => IsWeightedHomogeneous.prod _ _ _ (fun c _ =>
      ((isWeightedHomogeneous_X _ ω _).pow _).mul ((isWeightedHomogeneous_X _ ω _).pow _)))
  have h2 : IsWeightedHomogeneous ω (∏ c : Fin (X.m + 1),
      ((MvPolynomial.X ((topEnd X j, true), c) : RHH O X) ^ A ((topEnd X j, true), c) *
        MvPolynomial.X ((topEnd X j, false), c) ^ A ((topEnd X j, false), c)))
      (∑ c : Fin (X.m + 1), (A ((topEnd X j, true), c) • ω ((topEnd X j, true), c) +
          A ((topEnd X j, false), c) • ω ((topEnd X j, false), c))) :=
    IsWeightedHomogeneous.prod _ _ _ (fun c _ =>
      ((isWeightedHomogeneous_X _ ω _).pow _).mul ((isWeightedHomogeneous_X _ ω _).pow _))
  exact h1.mul h2

theorem tg_head_wh (L : LvDat C0 CE1 CE2 mu X β) (j : Fin (numSeg X.TT)) (ju : Fin (X.seg C0 CE1 CE2 j).t → ℕ)
    (Gu : MvPolynomial (Fin (2 * segS X.TT j + 1) × Fin X.m) (KK O)) (du : Fin (2 * segS X.TT j + 1) → ℕ)
    (hG : Gu ∈ Pol (KK O) X.m du)
    (ω : (X.TT × Bool) × Fin (X.m + 1) → ℕ) (hc : ∀ x (c c' : Fin X.m), ω (x, c.succ) = ω (x, c'.succ))
    (hU : ∀ i : Fin (segS X.TT j),
      ω ((topOdd X j i, true), 0) + ω ((topOdd X j i, false), 0) =
      ω ((topOdd X j i, true), Fin.succ 0) + ω ((topOdd X j i, false), Fin.succ 0))
    (hP : ω ((topEnd X j, true), 0) + ω ((topEnd X j, false), 0) =
      ω ((topEnd X j, true), Fin.succ 0) + ω ((topEnd X j, false), Fin.succ 0)) :
    IsWeightedHomogeneous ω (L.head O j ju Gu) (tgHD L j ju du ω) := by
  let ω' : BVar (2 * segS X.TT j + 1) X.m (X.seg C0 CE1 CE2 j).t → ℕ :=
    fun v => symLev X.p C0 CE1 CE2 X j v * ω (symVar C0 CE1 CE2 X j v)
  let ωL : Fin (2 * segS X.TT j + 1 + 1) → ℕ := fun a => ω' (Sum.inl (a, 0))
  have h1 : ∀ a c, ω' (Sum.inl (a, c)) = ωL a := by
    intro a c
    simp only [ω', ωL, symLev, symVar]
    split_ifs <;> rw [hc _ c 0]
  have e0 : ∀ i : Fin (segS X.TT j), finPos (2 * segS X.TT j + 1) (2 * (i : ℕ)) =
      Fin.castSucc (⟨2 * i.val, by omega⟩ : Fin (2 * segS X.TT j + 1)) := by
    intro i
    have := i.2
    apply Fin.ext
    show min (2 * i.val) (2 * segS X.TT j + 1) = 2 * i.val
    omega
  have e1 : ∀ i : Fin (segS X.TT j), finPos (2 * segS X.TT j + 1) (2 * (i : ℕ) + 1) =
      Fin.castSucc (⟨2 * i.val + 1, by omega⟩ : Fin (2 * segS X.TT j + 1)) := by
    intro i
    have := i.2
    apply Fin.ext
    show min (2 * i.val + 1) (2 * segS X.TT j + 1) = 2 * i.val + 1
    omega
  have hW : ∀ i : Fin (segS X.TT j), ωL (Fin.castSucc (⟨2 * i.val, by omega⟩ : Fin (2 * segS X.TT j + 1))) =
      (X.seg C0 CE1 CE2 j).P X.p i * ω ((topOdd X j i, true), Fin.succ 0) := by
    intro i
    simp only [ωL, ω']
    rw [symbol_variable_lower_letter, symbol_level_lower_letter]
  have hE : ∀ i : Fin (segS X.TT j), ωL (Fin.castSucc (⟨2 * i.val + 1, by omega⟩ : Fin (2 * segS X.TT j + 1))) =
      (X.seg C0 CE1 CE2 j).P X.p i * ω ((topOdd X j i, false), Fin.succ 0) := by
    intro i
    simp only [ωL, ω']
    rw [sv_E, sl_E]
  have hUU : ωL (Fin.castSucc (⟨2 * segS X.TT j, by omega⟩ : Fin (2 * segS X.TT j + 1))) =
      ω ((topEnd X j, true), Fin.succ 0) := by
    simp only [ωL, ω']
    rw [sv_U, sl_U, one_mul]
  have hXi : ωL (Fin.last _) = ω ((topEnd X j, false), Fin.succ 0) := by
    simp only [ωL, ω']
    rw [sv_xi, sl_xi, one_mul]
  have hZ : ∀ (l : Fin (X.seg C0 CE1 CE2 j).t) (β : Bool), ω' (Sum.inr (Fin.castSucc l, β)) =
      (X.seg C0 CE1 CE2 j).P X.p (uTop (X.seg C0 CE1 CE2 j) l) * ω ((topOdd X j (uTop (X.seg C0 CE1 CE2 j) l), !β), 0) := by
    intro l β
    simp only [ω']
    rw [sv_Z, sl_Z]
  have hx : ∀ β : Bool, ω' (Sum.inr (Fin.last (X.seg C0 CE1 CE2 j).t, β)) = ω ((topEnd X j, !β), 0) := by
    intro β
    simp only [ω']
    rw [symbol_variable_last, symbol_level_last, one_mul]
  have h2 : ∀ l : Fin (X.seg C0 CE1 CE2 j).t, ω' (Sum.inr (Fin.castSucc l, false)) + ω' (Sum.inr (Fin.castSucc l, true)) =
      ωL (finPos (2 * segS X.TT j + 1) (2 * (uTop (X.seg C0 CE1 CE2 j) l : ℕ))) +
        ωL (finPos (2 * segS X.TT j + 1) (2 * (uTop (X.seg C0 CE1 CE2 j) l : ℕ) + 1)) := by
    intro l
    rw [hZ, hZ, e0, e1, hW, hE, ← mul_add, ← mul_add]
    congr 1
    exact hU _
  have h3 : ω' (Sum.inr (Fin.last (X.seg C0 CE1 CE2 j).t, false)) + ω' (Sum.inr (Fin.last (X.seg C0 CE1 CE2 j).t, true)) =
      ωL (Fin.castSucc ⟨2 * segS X.TT j, by omega⟩) + ωL (Fin.last _) := by
    rw [hx, hx, hUU, hXi]
    exact hP
  have hEh : ∀ l : Fin (X.seg C0 CE1 CE2 j).t, IsWeightedHomogeneous ω' ((BDk C0 CE1 CE2 mu X β j).Ehat O (r := X.m) l)
      (ωL (finPos (2 * segS X.TT j + 1) (2 * (uTop (X.seg C0 CE1 CE2 j) l : ℕ))) +
        ωL (finPos (2 * segS X.TT j + 1) (2 * (uTop (X.seg C0 CE1 CE2 j) l : ℕ) + 1))) := by
    intro l
    refine IsWeightedHomogeneous.add ?_ (IsWeightedHomogeneous.sum _ _ _ fun c _ => ?_)
    · rw [← h2 l]
      exact (isWeightedHomogeneous_X _ ω' _).mul (isWeightedHomogeneous_X _ ω' _)
    · have := (isWeightedHomogeneous_X (KK O) ω' (Sum.inl (finPos (2 * segS X.TT j + 1)
          (2 * (uTop (X.seg C0 CE1 CE2 j) l : ℕ)), c))).mul
        (isWeightedHomogeneous_X (KK O) ω' (Sum.inl (finPos (2 * segS X.TT j + 1)
          (2 * (uTop (X.seg C0 CE1 CE2 j) l : ℕ) + 1), c)))
      rw [h1, h1] at this
      exact this
  have hEp : IsWeightedHomogeneous ω' ((BDk C0 CE1 CE2 mu X β j).Eplus O (r := X.m))
      (ωL (Fin.castSucc ⟨2 * segS X.TT j, by omega⟩) + ωL (Fin.last _)) := by
    refine IsWeightedHomogeneous.add ?_ (IsWeightedHomogeneous.sum _ _ _ fun c _ => ?_)
    · rw [← h3]
      exact (isWeightedHomogeneous_X _ ω' _).mul (isWeightedHomogeneous_X _ ω' _)
    · have := (isWeightedHomogeneous_X (KK O) ω' (Sum.inl (Fin.castSucc (⟨2 * segS X.TT j, by omega⟩ :
          Fin (2 * segS X.TT j + 1)), c))).mul
        (isWeightedHomogeneous_X (KK O) ω' (Sum.inl (Fin.last (2 * segS X.TT j + 1), c)))
      rw [h1, h1] at this
      exact this
  have hA := IsWeightedHomogeneous.prod Finset.univ
    (fun l : Fin (X.seg C0 CE1 CE2 j).t => (BDk C0 CE1 CE2 mu X β j).Ehat O (r := X.m) l ^ ju l) _
    (fun l _ => (hEh l).pow (ju l))
  have hB := hEp.pow (L.jp j)
  have hY := wh_chain (t := (X.seg C0 CE1 CE2 j).t) ω' ωL h1 du Gu hG
  have hall := (hA.mul hB).mul hY
  have hfin := wh_aeval ω (symVar C0 CE1 CE2 X j) (symLev X.p C0 CE1 CE2 X j) _ _ hall
  refine wh_congr hfin ?_
  have hs1 : ∑ a : Fin (2 * segS X.TT j + 1), jE (X.seg C0 CE1 CE2 j) ju (a.val / 2) * ωL (Fin.castSucc a) =
      ∑ i : Fin (segS X.TT j), (jE (X.seg C0 CE1 CE2 j) ju i.val *
          ((X.seg C0 CE1 CE2 j).P X.p i * ω ((topOdd X j i, true), Fin.succ 0)) +
        jE (X.seg C0 CE1 CE2 j) ju i.val * ((X.seg C0 CE1 CE2 j).P X.p i * ω ((topOdd X j i, false), Fin.succ 0))) := by
    rw [sum_chain]
    have t0 : jE (X.seg C0 CE1 CE2 j) ju ((2 * segS X.TT j) / 2) = 0 := by
      rw [Nat.mul_div_cancel_left _ (by norm_num)]; exact jE_top _ ju
    show (∑ i : Fin (segS X.TT j), (jE (X.seg C0 CE1 CE2 j) ju ((2 * i.val) / 2) * ωL _ +
      jE (X.seg C0 CE1 CE2 j) ju ((2 * i.val + 1) / 2) * ωL _)) + jE (X.seg C0 CE1 CE2 j) ju ((2 * segS X.TT j) / 2) * ωL _ = _
    rw [t0, zero_mul, add_zero]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hW, hE, show 2 * i.val / 2 = i.val by omega, show (2 * i.val + 1) / 2 = i.val by omega]
  have hs2 : ∑ a : Fin (2 * segS X.TT j + 1), du a * ωL (Fin.castSucc a) =
      ∑ i : Fin (segS X.TT j), (du (chW i) * ((X.seg C0 CE1 CE2 j).P X.p i * ω ((topOdd X j i, true), Fin.succ 0)) +
        du (chE i) * ((X.seg C0 CE1 CE2 j).P X.p i * ω ((topOdd X j i, false), Fin.succ 0))) +
      du (chU _) * ω ((topEnd X j, true), Fin.succ 0) := by
    rw [sum_chain, hUU]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hW, hE]
    rfl
  simp only [smul_eq_mul]
  rw [← tie_sum (X.seg C0 CE1 CE2 j) ju ωL, hs1, hs2, hUU, hXi]
  unfold tgHD
  have e : ∑ i : Fin (segS X.TT j), (X.seg C0 CE1 CE2 j).P X.p i *
      ((jE (X.seg C0 CE1 CE2 j) ju i.val + du (chW i)) * ω ((topOdd X j i, true), Fin.succ 0) +
        (jE (X.seg C0 CE1 CE2 j) ju i.val + du (chE i)) * ω ((topOdd X j i, false), Fin.succ 0)) =
      ∑ i : Fin (segS X.TT j), (jE (X.seg C0 CE1 CE2 j) ju i.val *
          ((X.seg C0 CE1 CE2 j).P X.p i * ω ((topOdd X j i, true), Fin.succ 0)) +
        jE (X.seg C0 CE1 CE2 j) ju i.val * ((X.seg C0 CE1 CE2 j).P X.p i * ω ((topOdd X j i, false), Fin.succ 0))) +
      ∑ i : Fin (segS X.TT j), (du (chW i) * ((X.seg C0 CE1 CE2 j).P X.p i * ω ((topOdd X j i, true), Fin.succ 0)) +
        du (chE i) * ((X.seg C0 CE1 CE2 j).P X.p i * ω ((topOdd X j i, false), Fin.succ 0))) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [e]
  ring

end

def tgWN (X : Loc) : (X.TT × Bool) × Fin (X.m + 1) → ℕ := fun v =>
  if ((hhLetters X.TT).vec v.1 = true ∧ 1 ≤ v.2.val) ∨ ((hhLetters X.TT).vec v.1 = false ∧ v.2.val < 1) then 1 else 0

theorem weight_tgWN (X : Loc) (m : MonH X) : Finsupp.weight (tgWN X) m = ndM X m := by
  unfold ndM degUS
  rw [Finsupp.weight_apply, Finsupp.sum]
  refine Finset.sum_congr rfl fun v _ => ?_
  unfold tgWN
  by_cases h : ((hhLetters X.TT).vec v.1 = true ∧ 1 ≤ v.2.val) ∨ ((hhLetters X.TT).vec v.1 = false ∧ v.2.val < 1)
  · rw [if_pos h, if_pos h, smul_eq_mul, mul_one]
  · rw [if_neg h, if_neg h, smul_eq_mul, mul_zero]

theorem tgWN_true_zero_eq_zero (X : Loc) (t : X.TT) : tgWN X ((t, true), 0) = 0 := by simp [tgWN, hhLetters]
theorem tgWN_ts (X : Loc) (t : X.TT) (c : Fin X.m) : tgWN X ((t, true), c.succ) = 1 := by simp [tgWN, hhLetters]
theorem top_weight_false_zero_eq_one (X : Loc) (t : X.TT) : tgWN X ((t, false), 0) = 1 := by simp [tgWN, hhLetters]
theorem tgWN_fs (X : Loc) (t : X.TT) (c : Fin X.m) : tgWN X ((t, false), c.succ) = 0 := by simp [tgWN, hhLetters]

theorem tg_nd_eval {C0 CE1 CE2 mu : ℝ} {X : Loc} [NeZero X.m] {β : GlobalTheory X} (L : LvDat C0 CE1 CE2 mu X β)
    (j : Fin (numSeg X.TT)) (ju : Fin (X.seg C0 CE1 CE2 j).t → ℕ) (du : Fin (2 * segS X.TT j + 1) → ℕ) (A : MonH X) :
    tgHD L j ju du (tgWN X) + tgWM X j A (tgWN X) =
      nuSeg C0 CE1 CE2 X j ju (L.jp j) du A + A ((topEnd X j, false), 0) := by
  unfold tgHD tgWM nuSeg
  simp only [Fin.sum_univ_succ, tgWN_true_zero_eq_zero, tgWN_ts, top_weight_false_zero_eq_one, tgWN_fs, mul_one, mul_zero, add_zero, zero_add,
    Finset.sum_add_distrib, Finset.sum_const_zero]
  ring

end Formalism.MainNotions.ColumnSystems.Pf
