import Formalism.LocalToGlobal.CharacterGerms.RowTiePLSmallCv

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace Formalism.L2.FormalSeriesBounds

namespace RowTiePLSmall

open PartialDerivEval RowTiePE0 RowTiePProj

section Main

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}

theorem lg_const (Y : FBChart C V O dd) (i : Fin dd) : constantCoeff (Y.lg i) = 0 := by
  have h := Y.lg_lin i 0 (by simp)
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, h]
  simp [MvPowerSeries.coeff_X]
  exact (Finsupp.single_ne_zero.2 one_ne_zero).symm

theorem germEval_oneStandardPoint_self (f : PS C 1 dd) : ev (n := 1) ![pt C dd 0] f = f := by
  unfold ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ.ev
  have : (fun p : Fin 1 × Fin dd => (![pt C dd 0] : Fin 1 → Pt C 1 dd) p.1 p.2) = X := by
    funext p
    obtain ⟨k, j⟩ := p
    fin_cases k
    rfl
  rw [this, subst_self]
  rfl

theorem formalGroupLaw_ev_x_zero (Y : FBChart C V O dd) {n : ℕ} (A : Pt C n dd) (hA : ∀ j, constantCoeff (A j) = 0) (i : Fin dd) :
    ev (![A, 0] : Fin 2 → Pt C n dd) (Y.B.G.F i) = A i := by
  have hZ : Z0 (![A, 0] : Fin 2 → Pt C n dd) := z0_p0 A hA
  conv_lhs => rw [← Y.B.G.comm i]
  rw [ev_ev (z0_pp 1 0) hZ]
  have e1 : (fun k j => ev (![A, 0] : Fin 2 → Pt C n dd) ((![pt C dd 1, pt C dd 0] : Fin 2 → Pt C 2 dd) k j)) =
      ![0, A] := by
    funext k j; fin_cases k
    · exact ev_X hZ 1 j
    · exact ev_X hZ 0 j
  rw [e1]
  have hB : Z0 (![A] : Fin 1 → Pt C n dd) := z0_1 _ hA
  have hU : Z0 (![0, pt C dd 0] : Fin 2 → Pt C 1 dd) := by
    intro k j; fin_cases k
    · simp
    · exact z0_pt 0 j
  have e2 : (![0, A] : Fin 2 → Pt C n dd) =
      fun k j => ev (![A] : Fin 1 → Pt C n dd) ((![0, pt C dd 0] : Fin 2 → Pt C 1 dd) k j) := by
    funext k j; fin_cases k
    · exact (ev_zero hB).symm
    · exact (ev_X hB 0 j).symm
  rw [e2, ← ev_ev hU hB, Y.B.G.unit i, ev_X hB]
  rfl

theorem lg_addOf (Y : FBChart C V O dd) {n : ℕ} (P Q : Pt C n dd) (hP : ∀ j, constantCoeff (P j) = 0)
    (hQ : ∀ j, constantCoeff (Q j) = 0) (i : Fin dd) :
    ev ![addOf Y.B.G.F P Q] (Y.lg i) = ev ![P] (Y.lg i) + ev ![Q] (Y.lg i) := by
  have hPQ : Z0 (![P, Q] : Fin 2 → Pt C n dd) := constant_zero_two_points P Q hP hQ
  have h := congrArg (ev (![P, Q] : Fin 2 → Pt C n dd)) (Y.lg_add i)
  rw [ev_add hPQ] at h
  have hA : Z0 (![addOf Y.B.G.F (pt C (n := 2) dd 0) (pt C (n := 2) dd 1)] : Fin 1 → Pt C 2 dd) :=
    z0_1 _ (fun j => const_addOf Y 0 1 j)
  rw [ev_ev hA hPQ, ev_ev (z0_1 _ (z0_pt 0)) hPQ, ev_ev (z0_1 _ (z0_pt 1)) hPQ] at h
  have e1 : (fun k j => ev (![P, Q] : Fin 2 → Pt C n dd)
      ((![addOf Y.B.G.F (pt C (n := 2) dd 0) (pt C (n := 2) dd 1)] : Fin 1 → Pt C 2 dd) k j)) =
      ![addOf Y.B.G.F P Q] := by
    funext k j
    rw [Fin.fin_one_eq_zero k]
    show ev (![P, Q] : Fin 2 → Pt C n dd) (ev ![pt C (n := 2) dd 0, pt C (n := 2) dd 1] (Y.B.G.F j)) =
      ev ![P, Q] (Y.B.G.F j)
    rw [ev_ev (z0_pp 0 1) hPQ]
    congr 1
    funext k' j'
    fin_cases k'
    · exact ev_X hPQ 0 j'
    · exact ev_X hPQ 1 j'
  have e2 : (fun k j => ev (![P, Q] : Fin 2 → Pt C n dd) ((![pt C (n := 2) dd 0] : Fin 1 → Pt C 2 dd) k j)) = ![P] := by
    funext k j
    rw [Fin.fin_one_eq_zero k]
    exact ev_X hPQ 0 j
  have e3 : (fun k j => ev (![P, Q] : Fin 2 → Pt C n dd) ((![pt C (n := 2) dd 1] : Fin 1 → Pt C 2 dd) k j)) = ![Q] := by
    funext k j
    rw [Fin.fin_one_eq_zero k]
    exact ev_X hPQ 1 j
  rw [e1, e2, e3] at h
  exact h

theorem lg_act_nat (Y : FBChart C V O dd) (k : ℕ) (i : Fin dd) :
    ev ![Y.B.A.act (k : O)] (Y.lg i) = MvPowerSeries.C (k : C) * Y.lg i := by
  have act0 := Y.B.A.const
  induction k with
  | zero =>
    have h0 : Y.B.A.act ((0 : ℕ) : O) = addOf Y.B.G.F (Y.B.A.act ((0 : ℕ) : O)) (Y.B.A.act ((0 : ℕ) : O)) := by
      have := Y.B.A.add_act 0 0
      rw [add_zero] at this
      rw [Nat.cast_zero]; exact this
    have h := lg_addOf Y (Y.B.A.act ((0 : ℕ) : O)) (Y.B.A.act ((0 : ℕ) : O)) (act0 _) (act0 _) i
    rw [← h0] at h
    simp only [Nat.cast_zero, map_zero, zero_mul] at h ⊢
    linear_combination -h
  | succ k ih =>
    have h1 : Y.B.A.act ((k + 1 : ℕ) : O) = addOf Y.B.G.F (Y.B.A.act (k : O)) (pt C dd 0) := by
      rw [Nat.cast_succ, Y.B.A.add_act, Y.B.A.one_act]
    rw [h1, lg_addOf Y _ _ (act0 _) (z0_pt 0) i, ih, germEval_oneStandardPoint_self, Nat.cast_succ, map_add, map_one]
    ring

theorem ex_lg_comp (Y : FBChart C V O dd) {n : ℕ} (φ : Pt C n dd) (hφ : ∀ j, constantCoeff (φ j) = 0) (i : Fin dd) :
    ev ![fun j => ev ![φ] (Y.lg j)] (Y.ex i) = φ i := by
  have hφ1 : Z0 (![φ] : Fin 1 → Pt C n dd) := z0_1 φ hφ
  have hlg : Z0 (![Y.lg] : Fin 1 → Pt C 1 dd) := z0_1 _ (lg_const Y)
  have e1 : (![fun j => ev ![φ] (Y.lg j)] : Fin 1 → Pt C n dd) =
      fun k j => ev (![φ] : Fin 1 → Pt C n dd) ((![Y.lg] : Fin 1 → Pt C 1 dd) k j) := by
    funext k j; rw [Fin.fin_one_eq_zero k]; rfl
  rw [e1, ← ev_ev hlg hφ1]
  have e2 : ev (![Y.lg] : Fin 1 → Pt C 1 dd) (Y.ex i) = pt C dd 0 i := congrFun Y.ex_lg i
  rw [e2]
  exact ev_X hφ1 0 i

end Main

end RowTiePLSmall

end Formalism.L2.FormalSeriesBounds
