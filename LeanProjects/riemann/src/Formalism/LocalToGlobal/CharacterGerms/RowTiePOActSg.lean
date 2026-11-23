import Formalism.LocalToGlobal.CharacterGerms.RowTiePOActLog
import Formalism.LocalToGlobal.CharacterGerms.RowTiePGerm

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace Formalism.L2.FormalSeriesBounds

namespace OActSg

open PartialDerivEval LogEx OActLog

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}

theorem actK_self (B : FB C dd O) (a : O) : B.actK C a = B.A.act a := by
  funext i
  simp [FB.actK, Algebra.algebraMap_self]

theorem pderiv_second_eval_first (f : PS C 1 dd) (i : Fin dd) : pderiv C ((1 : Fin 2), i) (ev (n := 2) ![pt C dd 0] f) = 0 := by
  rw [pderiv_eval_single (pt C dd 0) (coordinate_point_constantCoeff 0), sum_d_pt_other (0 : Fin 2) 1 (by decide)]

theorem pderiv_second_eval_second (f : PS C 1 dd) (i : Fin dd) :
    pderiv C ((1 : Fin 2), i) (ev (n := 2) ![pt C dd 1] f) = ev (n := 2) ![pt C dd 1] (pderiv C ((0 : Fin 1), i) f) := by
  rw [pderiv_eval_single (pt C dd 1) (coordinate_point_constantCoeff 1), sum_d_pt_self]

theorem eval_first_then_zero (f : PS C 1 dd) : ev (n := 1) ![pt C dd 0, 0] (ev (n := 2) ![pt C dd 0] f) = f := by
  have ha : MvPowerSeries.HasSubst
      (fun p : Fin 1 × Fin dd => (![pt C dd 0] : Fin 1 → Pt C 2 dd) p.1 p.2) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun p => by simp [pt])
  have hb : MvPowerSeries.HasSubst
      (fun p : Fin 2 × Fin dd => (![pt C dd 0, 0] : Fin 2 → Pt C 1 dd) p.1 p.2) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun p => by
      rcases p with ⟨j, i⟩
      fin_cases j <;> simp [pt])
  unfold ev
  rw [MvPowerSeries.subst_comp_subst_apply ha hb]
  have hX : (fun s : Fin 1 × Fin dd => MvPowerSeries.subst
      (fun p : Fin 2 × Fin dd => (![pt C dd 0, 0] : Fin 2 → Pt C 1 dd) p.1 p.2)
      ((![pt C dd 0] : Fin 1 → Pt C 2 dd) s.1 s.2)) = MvPowerSeries.X := by
    funext s
    rcases s with ⟨j, i⟩
    obtain rfl : j = 0 := Subsingleton.elim _ _
    show MvPowerSeries.subst (fun p : Fin 2 × Fin dd => (![pt C dd 0, 0] : Fin 2 → Pt C 1 dd) p.1 p.2)
      (MvPowerSeries.X ((0 : Fin 2), i)) = MvPowerSeries.X ((0 : Fin 1), i)
    rw [MvPowerSeries.subst_X hb]
    rfl
  rw [hX, MvPowerSeries.subst_self]
  rfl

theorem eval_second_then_zero (f : PS C 1 dd) :
    ev (n := 1) ![pt C dd 0, 0] (ev (n := 2) ![pt C dd 1] f) = MvPowerSeries.C (constantCoeff f) := by
  have ha : MvPowerSeries.HasSubst
      (fun p : Fin 1 × Fin dd => (![pt C dd 1] : Fin 1 → Pt C 2 dd) p.1 p.2) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun p => by simp [pt])
  have hb : MvPowerSeries.HasSubst
      (fun p : Fin 2 × Fin dd => (![pt C dd 0, 0] : Fin 2 → Pt C 1 dd) p.1 p.2) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun p => by
      rcases p with ⟨j, i⟩
      fin_cases j <;> simp [pt])
  unfold ev
  rw [MvPowerSeries.subst_comp_subst_apply ha hb]
  have hX : (fun s : Fin 1 × Fin dd => MvPowerSeries.subst
      (fun p : Fin 2 × Fin dd => (![pt C dd 0, 0] : Fin 2 → Pt C 1 dd) p.1 p.2)
      ((![pt C dd 1] : Fin 1 → Pt C 2 dd) s.1 s.2)) = 0 := by
    funext s
    rcases s with ⟨j, i⟩
    obtain rfl : j = 0 := Subsingleton.elim _ _
    show MvPowerSeries.subst (fun p : Fin 2 × Fin dd => (![pt C dd 0, 0] : Fin 2 → Pt C 1 dd) p.1 p.2)
      (MvPowerSeries.X ((1 : Fin 2), i)) = 0
    rw [MvPowerSeries.subst_X hb]
    rfl
  rw [hX, MvPowerSeries.subst_zero_eq_C_constantCoeff]
  simp

theorem sg_act (Y : FBChart C V O dd) (α : O) (v : Fin dd → C) (hv : ∀ i, V.Ge 0 (v i)) :
    IntS V (ev (n := 1) ![Y.B.A.act α] (Y.sgP v) - Y.sgP (linAct (Y.B.A.act (star α)) v)) := by
  set φ := Y.B.A.act α with hφdef
  set ψ := Y.B.A.act (star α) with hψdef
  have hφ0 : ∀ j, constantCoeff (φ j) = 0 := Y.B.A.const α
  have hψ0 : ∀ j, constantCoeff (ψ j) = 0 := Y.B.A.const (star α)
  set A : Pt C 2 dd := comp1 φ (pt C (n := 2) dd 0) with hA
  set Bp : Pt C 2 dd := comp1 ψ (pt C (n := 2) dd 1) with hBp
  have hA0 : ∀ j, constantCoeff (A j) = 0 := fun j => const_ev (z0_1 _ (coordinate_point_constantCoeff 0)) (hφ0 j)
  have hB0 : ∀ j, constantCoeff (Bp j) = 0 := fun j => const_ev (z0_1 _ (coordinate_point_constantCoeff 1)) (hψ0 j)
  have hZA : Z0 (![A, pt C dd 1] : Fin 2 → Pt C 2 dd) := by
    intro k j; fin_cases k
    · exact hA0 j
    · exact z0_pt 1 j
  have hZB : Z0 (![pt C dd 0, Bp] : Fin 2 → Pt C 2 dd) := by
    intro k j; fin_cases k
    · exact z0_pt 0 j
    · exact hB0 j
  set H : PS C 2 dd := ev (n := 2) ![A, pt C dd 1] Y.h - ev (n := 2) ![pt C dd 0, Bp] Y.h with hH
  have had : Y.B.ad α = FB.expS C H := by
    have := Y.gauge.ad α; rwa [toK_self, actK_self, actK_self] at this
  have hH0 : constantCoeff H = 0 := by
    rw [hH, map_sub, const_ev hZA (h_const Y), const_ev hZB (h_const Y), sub_zero]

  have t1 : ∀ i, ev (n := 1) ![pt C dd 0, 0] (pderiv C ((1 : Fin 2), i) (ev (n := 2) ![A, pt C dd 1] Y.h)) =
      ev (n := 1) ![φ, 0] (pderiv C ((1 : Fin 2), i) Y.h) := by
    intro i
    rw [pderiv_eval_pair hZA]
    have e1 : ∑ j, ev (n := 2) ![A, pt C dd 1] (pderiv C ((0 : Fin 2), j) Y.h) *
        pderiv C ((1 : Fin 2), i) ((![A, pt C dd 1] : Fin 2 → Pt C 2 dd) 0 j) = 0 :=
      Finset.sum_eq_zero fun j _ => by
        rw [show ((![A, pt C dd 1] : Fin 2 → Pt C 2 dd) 0 j) = ev (n := 2) ![pt C dd 0] (φ j) from rfl, pderiv_second_eval_first,
          mul_zero]
    rw [e1, zero_add]
    rw [show (∑ j, ev (n := 2) ![A, pt C dd 1] (pderiv C ((1 : Fin 2), j) Y.h) *
        pderiv C ((1 : Fin 2), i) ((![A, pt C dd 1] : Fin 2 → Pt C 2 dd) 1 j)) =
        ∑ j, ev (n := 2) ![A, pt C dd 1] (pderiv C ((1 : Fin 2), j) Y.h) * pderiv C ((1 : Fin 2), i) (pt C dd 1 j) from rfl,
      sum_d_pt_self]
    exact eval_eval_pair hZA constant_zero_first_zero (a' := φ) (b' := 0)
      (fun j => eval_first_then_zero (φ j)) (fun j => ev_X constant_zero_first_zero 1 j) _
  have t2 : ∀ i, ev (n := 1) ![pt C dd 0, 0] (pderiv C ((1 : Fin 2), i) (ev (n := 2) ![pt C dd 0, Bp] Y.h)) =
      ∑ j, ev (n := 1) ![pt C dd 0, 0] (pderiv C ((1 : Fin 2), j) Y.h) * MvPowerSeries.C (linM ψ j i) := by
    intro i
    rw [pderiv_eval_pair hZB]
    rw [show (∑ j, ev (n := 2) ![pt C dd 0, Bp] (pderiv C ((0 : Fin 2), j) Y.h) *
        pderiv C ((1 : Fin 2), i) ((![pt C dd 0, Bp] : Fin 2 → Pt C 2 dd) 0 j)) =
        ∑ j, ev (n := 2) ![pt C dd 0, Bp] (pderiv C ((0 : Fin 2), j) Y.h) * pderiv C ((1 : Fin 2), i) (pt C dd 0 j) from rfl,
      sum_d_pt_other (0 : Fin 2) 1 (by decide), zero_add, ev_sum constant_zero_first_zero]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [show ((![pt C dd 0, Bp] : Fin 2 → Pt C 2 dd) 1 j) = ev (n := 2) ![pt C dd 1] (ψ j) from rfl, pderiv_second_eval_second,
      ev_mul constant_zero_first_zero, eval_second_then_zero, cc_pderiv]
    congr 1
    exact eval_eval_pair hZB constant_zero_first_zero (a' := pt C dd 0) (b' := 0) (fun k => ev_X constant_zero_first_zero 0 k)
      (fun k => by
        show ev (n := 1) ![pt C dd 0, 0] (ev (n := 2) ![pt C dd 1] (ψ k)) = 0
        rw [eval_second_then_zero, hψ0 k, map_zero]) _
  have hi : ∀ i, ev (n := 1) ![pt C dd 0, 0] (pderiv C ((1 : Fin 2), i) (Y.B.ad α)) =
      ev (n := 1) ![φ, 0] (pderiv C ((1 : Fin 2), i) Y.h) -
        ∑ j, ev (n := 1) ![pt C dd 0, 0] (pderiv C ((1 : Fin 2), j) Y.h) * MvPowerSeries.C (linM ψ j i) := by
    intro i
    rw [had, pderiv_expS hH0, ← had, ev_mul constant_zero_first_zero, Y.B.adjoint_zero_snd, one_mul, hH, map_sub, ev_sub constant_zero_first_zero, t1, t2]
  have hl : ∀ j, linAct ψ v j = ∑ i, linM ψ j i * v i := fun j => rfl
  have e : ∑ j, MvPowerSeries.C (linAct ψ v j) * ev (n := 1) ![pt C dd 0, 0] (pderiv C ((1 : Fin 2), j) Y.h) =
      ∑ i, MvPowerSeries.C (v i) *
        ∑ j, ev (n := 1) ![pt C dd 0, 0] (pderiv C ((1 : Fin 2), j) Y.h) * MvPowerSeries.C (linM ψ j i) := by
    simp only [hl, map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have key : ev (n := 1) ![φ] (Y.sgP v) - Y.sgP (linAct ψ v) =
      -∑ i, MvPowerSeries.C (v i) * ev (n := 1) ![pt C dd 0, 0] (pderiv C ((1 : Fin 2), i) (Y.B.ad α)) := by
    rw [ev_sgP Y v φ hφ0, show Y.sgP (linAct ψ v) = -∑ j, MvPowerSeries.C (linAct ψ v j) *
        ev (n := 1) ![pt C dd 0, 0] (pderiv C ((1 : Fin 2), j) Y.h) from rfl, e]
    simp only [hi, mul_sub, Finset.sum_sub_distrib]
    ring
  rw [key]
  have hpts : ∀ k i, IntS V ((![pt C dd 0, 0] : Fin 2 → Pt C 1 dd) k i) := by
    intro k i; fin_cases k
    · exact intS_X _
    · exact intS_zero
  exact intS_neg (intS_sum _ fun i _ => intS_C_mul (hv i) (intS_ev constant_zero_first_zero hpts (intS_pderiv (Y.intAd α) _)))

end OActSg

end Formalism.L2.FormalSeriesBounds
