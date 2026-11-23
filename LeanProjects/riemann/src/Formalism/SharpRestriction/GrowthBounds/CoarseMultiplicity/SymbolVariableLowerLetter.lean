import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.DegSplit
import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.TopOddNeEnd

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial

theorem wh_aeval {K : Type} [CommRing K] {σ τ : Type} (ω : τ → ℕ) (f : σ → τ) (lev : σ → ℕ) (u : MvPolynomial σ K) (n : ℕ)
    (h : IsWeightedHomogeneous (fun v => lev v * ω (f v)) u n) :
    IsWeightedHomogeneous ω (aeval (fun v => (X (f v) : MvPolynomial τ K) ^ lev v) u) n := by
  have e : aeval (fun v => (X (f v) : MvPolynomial τ K) ^ lev v) u =
      ∑ μ ∈ u.support, aeval (fun v => (X (f v) : MvPolynomial τ K) ^ lev v) (monomial μ (u.coeff μ)) := by
    conv_lhs => rw [← support_sum_monomial_coeff u]
    rw [map_sum]
  rw [e]
  refine IsWeightedHomogeneous.sum _ _ _ fun μ hμ => ?_
  rw [aeval_monomial, MvPolynomial.algebraMap_eq, Finsupp.prod]
  have hw : Finsupp.weight (fun v => lev v * ω (f v)) μ = n := h (mem_support_iff.1 hμ)
  have h1 := IsWeightedHomogeneous.prod μ.support (fun v => ((X (f v) : MvPolynomial τ K) ^ lev v) ^ μ v) _
    (fun v _ => ((isWeightedHomogeneous_X K ω (f v)).pow (lev v)).pow (μ v))
  have h2 := (isWeightedHomogeneous_C ω (u.coeff μ)).mul h1
  refine wh_congr h2 ?_
  rw [zero_add, ← hw, Finsupp.weight_apply, Finsupp.sum]
  simp only [smul_eq_mul]

theorem sum_chain {s : ℕ} (f : Fin (2 * s + 1) → ℕ) :
    ∑ a, f a = ∑ i : Fin s, (f ⟨2 * i.val, by omega⟩ + f ⟨2 * i.val + 1, by omega⟩) + f ⟨2 * s, by omega⟩ := by
  let F : ℕ → ℕ := fun k => if h : k < 2 * s + 1 then f ⟨k, h⟩ else 0
  have e1 : ∑ a, f a = ∑ k ∈ Finset.range (2 * s + 1), F k := by
    rw [Finset.sum_range]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [F]
    rw [dif_pos a.2]
  have e2 : ∀ n, ∑ k ∈ Finset.range (2 * n + 1), F k = ∑ i ∈ Finset.range n, (F (2 * i) + F (2 * i + 1)) + F (2 * n) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have h2 : 2 * (n + 1) = 2 * n + 1 + 1 := by ring
      rw [h2, Finset.sum_range_succ, Finset.sum_range_succ, ih, Finset.sum_range_succ]
      ring
  rw [e1, e2 s, Finset.sum_range]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    have := i.2
    simp only [F]
    rw [dif_pos (by omega), dif_pos (by omega)]
  · simp only [F]
    rw [dif_pos (by omega)]

theorem sum_uTop {s : ℕ} (S : SegData s) (g : Fin s → ℕ) :
    ∑ l : Fin S.t, g (uTop S l) = ∑ i : Fin s, if S.sigma ≤ i.val then g i else 0 := by
  rw [← Finset.sum_filter]
  refine Finset.sum_nbij (fun l => uTop S l) ?_ ?_ ?_ (fun _ _ => rfl)
  · intro l _
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, Nat.le_add_right _ _⟩
  · intro l _ l' _ h
    apply Fin.ext
    have h' : S.sigma + l.val = S.sigma + l'.val := congrArg Fin.val h
    omega
  · intro i hi
    have hi' := (Finset.mem_filter.1 (Finset.mem_coe.1 hi)).2
    have := i.2
    exact ⟨⟨i.val - S.sigma, by unfold SegData.t; omega⟩, Finset.mem_coe.2 (Finset.mem_univ _),
      Fin.ext (by show S.sigma + (i.val - S.sigma) = i.val; omega)⟩

section Sym

variable (C0 CE1 CE2 : ℝ) (X : Loc) (j : Fin (numSeg X.TT))

theorem sv_Z (l : Fin (X.seg C0 CE1 CE2 j).t) (β : Bool) :
    symVar C0 CE1 CE2 X j (Sum.inr (Fin.castSucc l, β)) = ((topOdd X j (uTop (X.seg C0 CE1 CE2 j) l), !β), 0) := by
  simp only [symVar]
  rw [dif_pos (show ((Fin.castSucc l : Fin _) : ℕ) < _ from l.2)]
  rfl

theorem sl_Z (l : Fin (X.seg C0 CE1 CE2 j).t) (β : Bool) :
    symLev X.p C0 CE1 CE2 X j (Sum.inr (Fin.castSucc l, β)) =
      (X.seg C0 CE1 CE2 j).P X.p (uTop (X.seg C0 CE1 CE2 j) l) := by
  simp only [symLev]
  rw [dif_pos (show ((Fin.castSucc l : Fin _) : ℕ) < _ from l.2)]
  rfl

theorem symbol_variable_last (β : Bool) :
    symVar C0 CE1 CE2 X j (Sum.inr (Fin.last _, β)) = ((topEnd X j, !β), 0) := by
  simp only [symVar]
  rw [dif_neg (hnc := by show ¬ ((Fin.last (X.seg C0 CE1 CE2 j).t : Fin _) : ℕ) < _; exact lt_irrefl _)]

theorem symbol_level_last (β : Bool) : symLev X.p C0 CE1 CE2 X j (Sum.inr (Fin.last _, β)) = 1 := by
  simp only [symLev]
  rw [dif_neg (hnc := by show ¬ ((Fin.last (X.seg C0 CE1 CE2 j).t : Fin _) : ℕ) < _; exact lt_irrefl _)]

theorem symbol_variable_lower_letter (i : Fin (segS X.TT j)) (c : Fin X.m) :
    symVar C0 CE1 CE2 X j (Sum.inl (Fin.castSucc (⟨2 * i.val, by omega⟩ : Fin (2 * segS X.TT j + 1)), c)) =
      ((topOdd X j i, true), c.succ) := by
  have hi := i.2
  simp only [symVar]
  rw [dif_pos (hc := by show 2 * i.val < 2 * segS X.TT j; omega)]
  have e1 : (⟨(2 * i.val) / 2, by omega⟩ : Fin (segS X.TT j)) = i := Fin.ext (by show 2 * i.val / 2 = i.val; omega)
  have e2 : decide ((2 * i.val) % 2 = 0) = true := by simp
  show ((topOdd X j ⟨(2 * i.val) / 2, _⟩, decide ((2 * i.val) % 2 = 0)), c.succ) = _
  rw [e1, e2]

theorem symbol_level_lower_letter (i : Fin (segS X.TT j)) (c : Fin X.m) :
    symLev X.p C0 CE1 CE2 X j (Sum.inl (Fin.castSucc (⟨2 * i.val, by omega⟩ : Fin (2 * segS X.TT j + 1)), c)) =
      (X.seg C0 CE1 CE2 j).P X.p i := by
  have hi := i.2
  simp only [symLev]
  rw [dif_pos (hc := by show 2 * i.val < 2 * segS X.TT j; omega)]
  have e1 : (⟨(2 * i.val) / 2, by omega⟩ : Fin (segS X.TT j)) = i := Fin.ext (by show 2 * i.val / 2 = i.val; omega)
  show (X.seg C0 CE1 CE2 j).P X.p ⟨(2 * i.val) / 2, _⟩ = _
  rw [e1]

theorem sv_E (i : Fin (segS X.TT j)) (c : Fin X.m) :
    symVar C0 CE1 CE2 X j (Sum.inl (Fin.castSucc (⟨2 * i.val + 1, by omega⟩ : Fin (2 * segS X.TT j + 1)), c)) =
      ((topOdd X j i, false), c.succ) := by
  have hi := i.2
  simp only [symVar]
  rw [dif_pos (hc := by show 2 * i.val + 1 < 2 * segS X.TT j; omega)]
  have e1 : (⟨(2 * i.val + 1) / 2, by omega⟩ : Fin (segS X.TT j)) = i :=
    Fin.ext (by show (2 * i.val + 1) / 2 = i.val; omega)
  have e2 : decide ((2 * i.val + 1) % 2 = 0) = false := by
    rw [decide_eq_false_iff_not]
    omega
  show ((topOdd X j ⟨(2 * i.val + 1) / 2, _⟩, decide ((2 * i.val + 1) % 2 = 0)), c.succ) = _
  rw [e1, e2]

theorem sl_E (i : Fin (segS X.TT j)) (c : Fin X.m) :
    symLev X.p C0 CE1 CE2 X j (Sum.inl (Fin.castSucc (⟨2 * i.val + 1, by omega⟩ : Fin (2 * segS X.TT j + 1)), c)) =
      (X.seg C0 CE1 CE2 j).P X.p i := by
  have hi := i.2
  simp only [symLev]
  rw [dif_pos (hc := by show 2 * i.val + 1 < 2 * segS X.TT j; omega)]
  have e1 : (⟨(2 * i.val + 1) / 2, by omega⟩ : Fin (segS X.TT j)) = i :=
    Fin.ext (by show (2 * i.val + 1) / 2 = i.val; omega)
  show (X.seg C0 CE1 CE2 j).P X.p ⟨(2 * i.val + 1) / 2, _⟩ = _
  rw [e1]

theorem sv_U (c : Fin X.m) :
    symVar C0 CE1 CE2 X j (Sum.inl (Fin.castSucc (⟨2 * segS X.TT j, by omega⟩ : Fin (2 * segS X.TT j + 1)), c)) =
      ((topEnd X j, true), c.succ) := by
  simp only [symVar]
  rw [dif_neg (hnc := by show ¬ 2 * segS X.TT j < 2 * segS X.TT j; exact lt_irrefl _)]
  show ((topEnd X j, decide (2 * segS X.TT j = 2 * segS X.TT j)), c.succ) = _
  simp

theorem sl_U (c : Fin X.m) :
    symLev X.p C0 CE1 CE2 X j (Sum.inl (Fin.castSucc (⟨2 * segS X.TT j, by omega⟩ : Fin (2 * segS X.TT j + 1)), c)) = 1 := by
  simp only [symLev]
  rw [dif_neg (hnc := by show ¬ 2 * segS X.TT j < 2 * segS X.TT j; exact lt_irrefl _)]

theorem sv_xi (c : Fin X.m) :
    symVar C0 CE1 CE2 X j (Sum.inl (Fin.last (2 * segS X.TT j + 1), c)) = ((topEnd X j, false), c.succ) := by
  simp only [symVar]
  rw [dif_neg (hnc := by show ¬ 2 * segS X.TT j + 1 < 2 * segS X.TT j; omega)]
  show ((topEnd X j, decide (2 * segS X.TT j + 1 = 2 * segS X.TT j)), c.succ) = _
  simp

theorem sl_xi (c : Fin X.m) :
    symLev X.p C0 CE1 CE2 X j (Sum.inl (Fin.last (2 * segS X.TT j + 1), c)) = 1 := by
  simp only [symLev]
  rw [dif_neg (hnc := by show ¬ 2 * segS X.TT j + 1 < 2 * segS X.TT j; omega)]

end Sym

end Formalism.MainNotions.ColumnSystems.Pf
