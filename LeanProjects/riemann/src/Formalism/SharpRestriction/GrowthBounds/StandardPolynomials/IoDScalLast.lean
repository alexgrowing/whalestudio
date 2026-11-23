import Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.IoBlockNeZero

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial

section Io

variable {C0 CE1 CE2 mu : ℝ} {X : Loc} [NeZero X.m] {O : Type} [CommRing O] [IsDomain O] (β : GlobalTheory X) (j : Fin (numSeg X.TT))

theorem ioD_X (v : BVar (2 * segS X.TT j + 1) X.m (BDk C0 CE1 CE2 mu X β j).T.t) :
    ioD O C0 CE1 CE2 mu X β j (MvPolynomial.X v) =
      MvPolynomial.X (symVar C0 CE1 CE2 X j v) ^ symLev X.p C0 CE1 CE2 X j v := by
  unfold ioD ioA
  exact aeval_X _ _

theorem ioD_scal (l : Fin (BDk C0 CE1 CE2 mu X β j).T.t) (bb : Bool) :
    ioD O C0 CE1 CE2 mu X β j (MvPolynomial.X (Sum.inr (Fin.castSucc l, bb))) =
      MvPolynomial.X ((topOdd X j (uTop (X.seg C0 CE1 CE2 j) l), !bb), 0) ^
        (X.seg C0 CE1 CE2 j).P X.p (uTop (X.seg C0 CE1 CE2 j) l) := by
  rw [ioD_X]
  have hl : ((Fin.castSucc l : Fin ((BDk C0 CE1 CE2 mu X β j).T.t + 1)) : ℕ) < (X.seg C0 CE1 CE2 j).t := l.2
  simp only [symVar, symLev]
  rw [dif_pos hl, dif_pos hl]
  rfl

theorem ioD_scalLast (bb : Bool) :
    ioD O C0 CE1 CE2 mu X β j (MvPolynomial.X (Sum.inr (Fin.last (BDk C0 CE1 CE2 mu X β j).T.t, bb))) =
      MvPolynomial.X ((topEnd X j, !bb), 0) := by
  rw [ioD_X]
  have hl : ¬ ((Fin.last (BDk C0 CE1 CE2 mu X β j).T.t : Fin ((BDk C0 CE1 CE2 mu X β j).T.t + 1)) : ℕ) <
      (X.seg C0 CE1 CE2 j).t := lt_irrefl _
  simp only [symVar, symLev]
  rw [dif_neg hl, dif_neg hl, pow_one]

theorem ioD_odd (i : Fin (segS X.TT j)) (e : ℕ) (he : e < 2) (a : Fin (2 * segS X.TT j + 1 + 1)) (ha : (a : ℕ) = 2 * i + e)
    (c : Fin X.m) :
    ioD O C0 CE1 CE2 mu X β j (MvPolynomial.X (Sum.inl (a, c))) =
      MvPolynomial.X ((topOdd X j i, decide (e = 0)), c.succ) ^ (X.seg C0 CE1 CE2 j).P X.p i := by
  rw [ioD_X]
  have hi := i.2
  have hl : (a : ℕ) < 2 * segS X.TT j := by omega
  simp only [symVar, symLev]
  rw [dif_pos hl, dif_pos hl]
  have e1 : (⟨(a : ℕ) / 2, by omega⟩ : Fin (segS X.TT j)) = i := Fin.ext (by simp only; omega)
  have e2 : decide ((a : ℕ) % 2 = 0) = decide (e = 0) := by
    congr 1
    apply propext
    omega
  rw [e1, e2]

theorem ioD_end (e : ℕ) (he : e < 2) (a : Fin (2 * segS X.TT j + 1 + 1)) (ha : (a : ℕ) = 2 * segS X.TT j + e) (c : Fin X.m) :
    ioD O C0 CE1 CE2 mu X β j (MvPolynomial.X (Sum.inl (a, c))) =
      MvPolynomial.X ((topEnd X j, decide (e = 0)), c.succ) := by
  rw [ioD_X]
  have hl : ¬ (a : ℕ) < 2 * segS X.TT j := by omega
  simp only [symVar, symLev]
  rw [dif_neg hl, dif_neg hl, pow_one]
  have e2 : decide ((a : ℕ) = 2 * segS X.TT j) = decide (e = 0) := by
    congr 1
    apply propext
    omega
  rw [e2]

theorem ioD_Ehat (l : Fin (BDk C0 CE1 CE2 mu X β j).T.t) :
    ioD O C0 CE1 CE2 mu X β j ((BDk C0 CE1 CE2 mu X β j).Ehat O (r := X.m) l) =
      EhatT O X (topOdd X j (uTop (X.seg C0 CE1 CE2 j) l)) ((X.seg C0 CE1 CE2 j).P X.p (uTop (X.seg C0 CE1 CE2 j) l)) := by
  unfold BlockData.Ehat EhatT scalZ scalS
  rw [map_add, map_mul, map_sum, ioD_scal, ioD_scal]
  congr 1
  refine Finset.sum_congr rfl fun c _ => ?_
  have hu := (uTop (X.seg C0 CE1 CE2 j) l).2
  rw [map_mul, ioD_odd β j (uTop (X.seg C0 CE1 CE2 j) l) 0 (by omega) _ (by
      show min (2 * ((uTop (X.seg C0 CE1 CE2 j) l : Fin (segS X.TT j)) : ℕ)) (2 * segS X.TT j + 1) = _
      omega),
    ioD_odd β j (uTop (X.seg C0 CE1 CE2 j) l) 1 (by omega) _ (by
      show min (2 * ((uTop (X.seg C0 CE1 CE2 j) l : Fin (segS X.TT j)) : ℕ) + 1) (2 * segS X.TT j + 1) = _
      omega)]
  rfl

theorem ioD_Eplus :
    ioD O C0 CE1 CE2 mu X β j ((BDk C0 CE1 CE2 mu X β j).Eplus O (r := X.m)) = hTop O X (topEnd X j) := by
  unfold hTop hKey
  rw [Fin.sum_univ_succ]
  unfold BlockData.Eplus scalZ scalS xiVar
  rw [map_add, map_mul, map_sum, ioD_scalLast, ioD_scalLast]
  congr 1
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [map_mul, ioD_end β j 0 (by omega) _ (by rfl), ioD_end β j 1 (by omega) _ (by rfl)]
  rfl

end Io

theorem uTop_sum {s : ℕ} {M : Type} [AddCommMonoid M] (S : SegData s) (F : Fin s → M) :
    ∑ l : Fin S.t, F (uTop S l) = ∑ i : Fin s, if (i : ℕ) < S.sigma then 0 else F i := by
  classical
  have h1 : ∑ i : Fin s, (if (i : ℕ) < S.sigma then 0 else F i) =
      ∑ i ∈ Finset.univ.filter (fun i : Fin s => ¬ (i : ℕ) < S.sigma), F i := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases h : (i : ℕ) < S.sigma <;> simp [h]
  rw [h1]
  refine Finset.sum_bij (fun l _ => uTop S l) ?_ ?_ ?_ ?_
  · intro l _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, uTop]
    omega
  · intro l _ l' _ h
    have := congrArg Fin.val h
    simp only [uTop] at this
    exact Fin.ext (by omega)
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    refine ⟨⟨(i : ℕ) - S.sigma, ?_⟩, Finset.mem_univ _, ?_⟩
    · have := i.2
      unfold SegData.t
      omega
    · apply Fin.ext
      simp only [uTop]
      omega
  · intro l _
    rfl

end Formalism.MainNotions.ColumnSystems.Pf
