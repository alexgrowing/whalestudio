import Formalism.LocalToGlobal.CharacterGerms.RowTiePCEqDer

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace Formalism.L2.FormalSeriesBounds

open PartialDerivEval

namespace RowTiePCEqM

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}

theorem constant_zero_outer_points : Z0 ((![pt C dd 0, 0, pt C dd 1] : Fin 3 → Pt C 2 dd)) := by
  intro k i; fin_cases k <;> simp [pt]

theorem integral_outer_points : ∀ k i, IntS V (((![pt C dd 0, 0, pt C dd 1] : Fin 3 → Pt C 2 dd)) k i) := by
  intro k i; fin_cases k
  · exact intS_X _
  · exact intS_zero
  · exact intS_X _

theorem constant_zero_second_axis : Z0 ((![0, pt C dd 1] : Fin 2 → Pt C 2 dd)) := by
  intro k i; fin_cases k <;> simp [pt]

theorem integral_second_axis_points : ∀ k i, IntS V (((![0, pt C dd 1] : Fin 2 → Pt C 2 dd)) k i) := by
  intro k i; fin_cases k
  · exact intS_zero
  · exact intS_X _

theorem eval_outer_points_first (j : Fin dd) : ev (n := 2) ((![pt C dd 0, 0, pt C dd 1] : Fin 3 → Pt C 2 dd)) (pt C (n := 3) dd 0 j) = pt C dd 0 j := by
  rw [show (pt C (n := 3) dd 0 j) = X ((0 : Fin 3), j) from rfl, ev_X constant_zero_outer_points]; rfl

theorem eval_outer_points_middle (j : Fin dd) : ev (n := 2) ((![pt C dd 0, 0, pt C dd 1] : Fin 3 → Pt C 2 dd)) (pt C (n := 3) dd 1 j) = 0 := by
  rw [show (pt C (n := 3) dd 1 j) = X ((1 : Fin 3), j) from rfl, ev_X constant_zero_outer_points]; rfl

theorem eval_outer_points_last (j : Fin dd) : ev (n := 2) ((![pt C dd 0, 0, pt C dd 1] : Fin 3 → Pt C 2 dd)) (pt C (n := 3) dd 2 j) = pt C dd 1 j := by
  rw [show (pt C (n := 3) dd 2 j) = X ((2 : Fin 3), j) from rfl, ev_X constant_zero_outer_points]; rfl

theorem group_law_zero_right (Y : FBChart C V O dd) {n : ℕ} (P : Pt C n dd) (hP : ∀ j, constantCoeff (P j) = 0) (j : Fin dd) :
    ev (n := n) ![P, 0] (Y.B.G.F j) = P j := by
  have hA : Z0 (![P, 0] : Fin 2 → Pt C n dd) := z0_p0 P hP
  conv_lhs => rw [← Y.B.G.comm j]
  rw [ev_ev (z0_pp 1 0) hA]
  have e1 : (fun k i => ev (n := n) (![P, 0] : Fin 2 → Pt C n dd) ((![pt C dd 1, pt C dd 0] : Fin 2 → Pt C 2 dd) k i)) =
      ![0, P] := by
    funext k i; fin_cases k
    · exact ev_X hA 1 i
    · exact ev_X hA 0 i
  rw [e1]
  have hB : Z0 (![P] : Fin 1 → Pt C n dd) := z0_1 P hP
  have hU : Z0 (![0, pt C dd 0] : Fin 2 → Pt C 1 dd) := by
    intro k i; fin_cases k
    · simp
    · exact z0_pt 0 i
  have e2 : (![0, P] : Fin 2 → Pt C n dd) =
      fun k i => ev (n := n) (![P] : Fin 1 → Pt C n dd) ((![0, pt C dd 0] : Fin 2 → Pt C 1 dd) k i) := by
    funext k i; fin_cases k
    · exact (ev_zero hB).symm
    · exact (ev_X hB 0 i).symm
  rw [e2, ← ev_ev hU hB, Y.B.G.unit j, ev_X hB]
  rfl

theorem pderiv_ev_fst {n : ℕ} (A B : Pt C n dd) (hA : ∀ j, constantCoeff (A j) = 0) (hB : ∀ j, constantCoeff (B j) = 0)
    (q : Fin n × Fin dd) (hBq : ∀ j, pderiv C q (B j) = 0) (f : PS C 2 dd) :
    pderiv C q (ev ![A, B] f) = ∑ j, ev ![A, B] (pderiv C ((0 : Fin 2), j) f) * pderiv C q (A j) := by
  have hZ : Z0 (![A, B] : Fin 2 → Pt C n dd) := by
    intro k i; fin_cases k
    · exact hA i
    · exact hB i
  rw [pderiv_eval_pair hZ]
  have e : ∑ j, ev ![A, B] (pderiv C ((1 : Fin 2), j) f) * pderiv C q ((![A, B] : Fin 2 → Pt C n dd) 1 j) = 0 :=
    Finset.sum_eq_zero fun j _ => by
      rw [show ((![A, B] : Fin 2 → Pt C n dd) 1 j) = B j from rfl, hBq j, mul_zero]
  rw [e, add_zero]
  rfl

theorem pderiv_ev_snd {n : ℕ} (A B : Pt C n dd) (hA : ∀ j, constantCoeff (A j) = 0) (hB : ∀ j, constantCoeff (B j) = 0)
    (q : Fin n × Fin dd) (hAq : ∀ j, pderiv C q (A j) = 0) (f : PS C 2 dd) :
    pderiv C q (ev ![A, B] f) = ∑ j, ev ![A, B] (pderiv C ((1 : Fin 2), j) f) * pderiv C q (B j) := by
  have hZ : Z0 (![A, B] : Fin 2 → Pt C n dd) := by
    intro k i; fin_cases k
    · exact hA i
    · exact hB i
  rw [pderiv_eval_pair hZ]
  have e : ∑ j, ev ![A, B] (pderiv C ((0 : Fin 2), j) f) * pderiv C q ((![A, B] : Fin 2 → Pt C n dd) 0 j) = 0 :=
    Finset.sum_eq_zero fun j _ => by
      rw [show ((![A, B] : Fin 2 → Pt C n dd) 0 j) = A j from rfl, hAq j, mul_zero]
  rw [e, zero_add]
  rfl

theorem sum_pderiv_pt {n : ℕ} (k : Fin n) (i : Fin dd) (a : Fin dd → PS C n dd) :
    ∑ j, a j * pderiv C (k, i) (pt C dd k j) = a i := by
  rw [Finset.sum_eq_single i]
  · rw [show (pt C dd k i) = X (k, i) from rfl, pderiv_X_self, mul_one]
  · intro j _ hj
    rw [show (pt C dd k j) = X (k, j) from rfl, pderiv_X_of_ne (fun h => hj (Prod.mk.inj h).2), mul_zero]
  · intro h; exact absurd (Finset.mem_univ i) h

theorem pderiv_pt_ne {n : ℕ} {k k' : Fin n} (h : k' ≠ k) (i j : Fin dd) : pderiv C (k, i) (pt C dd k' j) = 0 :=
  pderiv_X_of_ne (fun e => h (Prod.mk.inj e).1)

end RowTiePCEqM

namespace RowTiePCEqM

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}

theorem hi1 (Y : FBChart C V O dd) (i : Fin dd) :
    ev (n := 2) (![pt C dd 0, 0, pt C dd 1] : Fin 3 → Pt C 2 dd) (pderiv C ((1 : Fin 3), i) Y.B.ph1) =
      ev (n := 2) (![0, pt C dd 1] : Fin 2 → Pt C 2 dd) (pderiv C ((0 : Fin 2), i) Y.h) -
        ∑ j, pderiv C ((0 : Fin 2), j) Y.h * ev (n := 2) ![pt C dd 0, 0] (pderiv C ((1 : Fin 2), i) (Y.B.G.F j)) := by
  have hph : Y.B.ph1 = FB.expS C (ev (n := 3) ![pt C dd 0, pt C dd 2] Y.h + ev (n := 3) ![pt C dd 1, pt C dd 2] Y.h -
      ev (n := 3) ![addOf Y.B.G.F (pt C dd 0) (pt C dd 1), pt C dd 2] Y.h) := by
    have := Y.gauge.ph1; rwa [toK_self, FK_self] at this
  have hg : constantCoeff (ev (n := 3) ![pt C dd 0, pt C dd 2] Y.h + ev (n := 3) ![pt C dd 1, pt C dd 2] Y.h -
      ev (n := 3) ![addOf Y.B.G.F (pt C dd 0) (pt C dd 1), pt C dd 2] Y.h) = 0 := by
    rw [map_sub, map_add, const_ev (killE.constant_zero_point_third _ (z0_pt 0)) (h_const Y),
      const_ev (killE.constant_zero_point_third _ (z0_pt 1)) (h_const Y), const_ev (killE.constant_zero_point_third _ (const_addOf Y 0 1)) (h_const Y)]
    simp
  have hd1 : ∀ k' : Fin 3, k' ≠ 1 → ∀ j, pderiv C ((1 : Fin 3), i) (pt C (n := 3) dd k' j) = 0 :=
    fun k' h j => pderiv_pt_ne h i j
  have hA : pderiv C ((1 : Fin 3), i) (ev (n := 3) ![pt C dd 0, pt C dd 2] Y.h) = 0 := by
    rw [pderiv_ev_fst _ _ (z0_pt 0) (z0_pt 2) _ (hd1 2 (by decide)) Y.h]
    exact Finset.sum_eq_zero fun j _ => by rw [hd1 0 (by decide) j, mul_zero]
  have hB : pderiv C ((1 : Fin 3), i) (ev (n := 3) ![pt C dd 1, pt C dd 2] Y.h) =
      ev (n := 3) ![pt C dd 1, pt C dd 2] (pderiv C ((0 : Fin 2), i) Y.h) := by
    rw [pderiv_ev_fst _ _ (z0_pt 1) (z0_pt 2) _ (hd1 2 (by decide)) Y.h, sum_pderiv_pt]
  have hFa : ∀ j, pderiv C ((1 : Fin 3), i) (addOf Y.B.G.F (pt C (n := 3) dd 0) (pt C dd 1) j) =
      ev (n := 3) ![pt C dd 0, pt C dd 1] (pderiv C ((1 : Fin 2), i) (Y.B.G.F j)) := by
    intro j
    show pderiv C _ (ev (n := 3) ![pt C dd 0, pt C dd 1] (Y.B.G.F j)) = _
    rw [pderiv_ev_snd _ _ (z0_pt 0) (z0_pt 1) _ (hd1 0 (by decide)) _, sum_pderiv_pt]
  have hC : pderiv C ((1 : Fin 3), i) (ev (n := 3) ![addOf Y.B.G.F (pt C dd 0) (pt C dd 1), pt C dd 2] Y.h) =
      ∑ j, ev (n := 3) ![addOf Y.B.G.F (pt C dd 0) (pt C dd 1), pt C dd 2] (pderiv C ((0 : Fin 2), j) Y.h) *
        ev (n := 3) ![pt C dd 0, pt C dd 1] (pderiv C ((1 : Fin 2), i) (Y.B.G.F j)) := by
    rw [pderiv_ev_fst _ _ (const_addOf Y 0 1) (z0_pt 2) _ (hd1 2 (by decide)) Y.h]
    simp only [hFa]
  have hE1B : ∀ f : PS C 2 dd, ev (n := 2) (![pt C dd 0, 0, pt C dd 1] : Fin 3 → Pt C 2 dd) (ev (n := 3) ![pt C dd 1, pt C dd 2] f) = ev (n := 2) (![0, pt C dd 1] : Fin 2 → Pt C 2 dd) f := by
    intro f
    rw [ev_ev (z0_pp 1 2) constant_zero_outer_points]
    congr 1
    funext k j; fin_cases k
    · exact eval_outer_points_middle j
    · exact eval_outer_points_last j
  have hE1F : ∀ j, ev (n := 2) (![pt C dd 0, 0, pt C dd 1] : Fin 3 → Pt C 2 dd) (addOf Y.B.G.F (pt C (n := 3) dd 0) (pt C dd 1) j) = pt C dd 0 j := by
    intro j
    show ev (n := 2) (![pt C dd 0, 0, pt C dd 1] : Fin 3 → Pt C 2 dd) (ev (n := 3) ![pt C dd 0, pt C dd 1] (Y.B.G.F j)) = _
    rw [ev_ev (z0_pp 0 1) constant_zero_outer_points]
    have e : (fun k j' => ev (n := 2) (![pt C dd 0, 0, pt C dd 1] : Fin 3 → Pt C 2 dd) ((![pt C dd 0, pt C dd 1] : Fin 2 → Pt C 3 dd) k j')) =
        ![pt C dd 0, 0] := by
      funext k j'; fin_cases k
      · exact eval_outer_points_first j'
      · exact eval_outer_points_middle j'
    rw [e, group_law_zero_right Y _ (z0_pt 0)]
  have hE1C : ∀ f : PS C 2 dd,
      ev (n := 2) (![pt C dd 0, 0, pt C dd 1] : Fin 3 → Pt C 2 dd) (ev (n := 3) ![addOf Y.B.G.F (pt C dd 0) (pt C dd 1), pt C dd 2] f) = f := by
    intro f
    rw [ev_ev (killE.constant_zero_point_third _ (const_addOf Y 0 1)) constant_zero_outer_points]
    have e : (fun k j => ev (n := 2) (![pt C dd 0, 0, pt C dd 1] : Fin 3 → Pt C 2 dd)
        ((![addOf Y.B.G.F (pt C dd 0) (pt C dd 1), pt C dd 2] : Fin 2 → Pt C 3 dd) k j)) = ![pt C dd 0, pt C dd 1] := by
      funext k j; fin_cases k
      · exact hE1F j
      · exact eval_outer_points_last j
    rw [e, eval_points_two]
  have hE1D : ∀ f : PS C 2 dd, ev (n := 2) (![pt C dd 0, 0, pt C dd 1] : Fin 3 → Pt C 2 dd) (ev (n := 3) ![pt C dd 0, pt C dd 1] f) =
      ev (n := 2) ![pt C dd 0, 0] f := by
    intro f
    rw [ev_ev (z0_pp 0 1) constant_zero_outer_points]
    congr 1
    funext k j; fin_cases k
    · exact eval_outer_points_first j
    · exact eval_outer_points_middle j
  rw [hph, pderiv_expS hg, ← hph, ev_mul constant_zero_outer_points, Y.B.cocycleLeft_zero_snd, one_mul, map_sub, map_add, ev_sub constant_zero_outer_points,
    ev_add constant_zero_outer_points, hA, ev_zero constant_zero_outer_points, zero_add, hB, hE1B, hC, ev_sum constant_zero_outer_points]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [ev_mul constant_zero_outer_points, hE1C, hE1D]

theorem hs1 (Y : FBChart C V O dd) (i : Fin dd) :
    ev (n := 2) (![0, pt C dd 1] : Fin 2 → Pt C 2 dd) (pderiv C ((0 : Fin 2), i) Y.B.sy) =
      ev (n := 2) ![pt C dd 1, 0] (pderiv C ((1 : Fin 2), i) Y.h) - ev (n := 2) (![0, pt C dd 1] : Fin 2 → Pt C 2 dd) (pderiv C ((0 : Fin 2), i) Y.h) := by
  have hsy : Y.B.sy = FB.expS C (ev (n := 2) ![pt C dd 1, pt C dd 0] Y.h - Y.h) := by
    have := Y.gauge.sy; rwa [toK_self] at this
  have hg : constantCoeff (ev (n := 2) ![pt C dd 1, pt C dd 0] Y.h - Y.h) = 0 := by
    rw [map_sub, const_ev (z0_pp 1 0) (h_const Y), h_const Y, sub_zero]
  have h1 : ev (n := 2) (![0, pt C dd 1] : Fin 2 → Pt C 2 dd) Y.B.sy = 1 := by
    have hB : Z0 (![pt C dd 1] : Fin 1 → Pt C 2 dd) := z0_1 _ (z0_pt 1)
    have hU : Z0 (![0, pt C dd 0] : Fin 2 → Pt C 1 dd) := by
      intro k i; fin_cases k
      · simp
      · exact z0_pt 0 i
    have e : (![0, pt C dd 1] : Fin 2 → Pt C 2 dd) = fun k j => ev (n := 2) (![pt C dd 1] : Fin 1 → Pt C 2 dd) ((![0, pt C dd 0] : Fin 2 → Pt C 1 dd) k j) := by
      funext k j; fin_cases k
      · exact (ev_zero hB).symm
      · exact (ev_X hB 0 j).symm
    rw [e, ← ev_ev hU hB, Y.B.symmetry_zero_fst, ev_eq_alg hB, map_one]
  have hd : pderiv C ((0 : Fin 2), i) (ev (n := 2) ![pt C dd 1, pt C dd 0] Y.h) =
      ev (n := 2) ![pt C dd 1, pt C dd 0] (pderiv C ((1 : Fin 2), i) Y.h) := by
    rw [pderiv_ev_snd _ _ (z0_pt 1) (z0_pt 0) _ (fun j => pderiv_pt_ne (by decide) i j) Y.h, sum_pderiv_pt]
  have hE : ∀ f : PS C 2 dd, ev (n := 2) (![0, pt C dd 1] : Fin 2 → Pt C 2 dd) (ev (n := 2) ![pt C dd 1, pt C dd 0] f) = ev (n := 2) ![pt C dd 1, 0] f := by
    intro f
    rw [ev_ev (z0_pp 1 0) constant_zero_second_axis]
    congr 1
    funext k j; fin_cases k
    · exact ev_X constant_zero_second_axis 1 j
    · exact ev_X constant_zero_second_axis 0 j
  rw [hsy, pderiv_expS hg, ← hsy, ev_mul constant_zero_second_axis, h1, one_mul, map_sub, ev_sub constant_zero_second_axis, hd, hE]

end RowTiePCEqM

open RowTiePCEqM

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}

theorem germIIM_holds (Y : FBChart C V O dd) : GermIIMSt Y := by
  intro v hv
  have key : (∑ j : Fin dd, (∑ i : Fin dd, MvPowerSeries.C (v i) *
        ev (n := 2) ![pt C dd 0, 0] (pderiv C ((1 : Fin 2), i) (Y.B.G.F j))) * pderiv C ((0 : Fin 2), j) Y.h) +
        ev (n := 2) ![pt C dd 1] (Y.sgP v) =
      -(∑ i, MvPowerSeries.C (v i) * ev (n := 2) (![pt C dd 0, 0, pt C dd 1] : Fin 3 → Pt C 2 dd) (pderiv C ((1 : Fin 3), i) Y.B.ph1)) +
        -∑ i, MvPowerSeries.C (v i) * ev (n := 2) (![0, pt C dd 1] : Fin 2 → Pt C 2 dd) (pderiv C ((0 : Fin 2), i) Y.B.sy) := by
    rw [ev_sgP Y v _ (z0_pt 1)]
    simp only [hi1, hs1, mul_sub, Finset.sum_sub_distrib, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm (s := (Finset.univ : Finset (Fin dd))) (t := (Finset.univ : Finset (Fin dd)))]
    have e : ∀ i j, MvPowerSeries.C (v i) * ev (n := 2) ![pt C dd 0, 0] (pderiv C ((1 : Fin 2), i) (Y.B.G.F j)) *
        pderiv C ((0 : Fin 2), j) Y.h = MvPowerSeries.C (v i) * (pderiv C ((0 : Fin 2), j) Y.h *
          ev (n := 2) ![pt C dd 0, 0] (pderiv C ((1 : Fin 2), i) (Y.B.G.F j))) := fun i j => by ring
    simp only [e]
    ring
  rw [key]
  exact intS_add (intS_neg (intS_sum _ fun i _ => intS_C_mul (hv i) (intS_ev constant_zero_outer_points integral_outer_points (intS_pderiv Y.intPh1 _))))
    (intS_neg (intS_sum _ fun i _ => intS_C_mul (hv i) (intS_ev constant_zero_second_axis integral_second_axis_points (intS_pderiv Y.intSy _))))

end Formalism.L2.FormalSeriesBounds
