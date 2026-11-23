import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MvIsIntMapMap

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IsoTriv

open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dAct)

theorem frame_cc_ev {C : Type} [CommRing C] {d m n : ℕ} (a : Fin m → Pt C n d)
    (ha : ∀ j i, constantCoeff (a j i) = 0) {f : PS C m d} (hf : constantCoeff f = 0) :
    constantCoeff (ev a f) = 0 := by
  have h0 : ∀ p : Fin m × Fin d, constantCoeff ((fun p : Fin m × Fin d => a p.1 p.2) p) = 0 := fun p => ha p.1 p.2
  unfold ev
  exact constantCoeff_subst_eq_zero (a := fun p : Fin m × Fin d => a p.1 p.2)
    (hasSubst_of_constantCoeff_zero h0) h0 hf

theorem frame_subst_ev {C : Type} [CommRing C] {d m n : ℕ} {σ : Type} (a : Fin m → Pt C n d)
    (ha : ∀ j i, constantCoeff (a j i) = 0) {t : Fin n × Fin d → MvPowerSeries σ C} (ht : HasSubst t)
    (f : PS C m d) :
    subst t (ev a f) = subst (fun p : Fin m × Fin d => subst t (a p.1 p.2)) f := by
  have h0 : ∀ p : Fin m × Fin d, constantCoeff ((fun p : Fin m × Fin d => a p.1 p.2) p) = 0 := fun p => ha p.1 p.2
  unfold ev
  exact subst_comp_subst_apply (a := fun p : Fin m × Fin d => a p.1 p.2) (hasSubst_of_constantCoeff_zero h0) ht f

theorem frame_cc_pt {C : Type} [CommRing C] {d n : ℕ} (b : Fin n) (j : Fin 1) (i : Fin d) :
    constantCoeff ((![pt C d b] : Fin 1 → Pt C n d) j i) = 0 := by
  simp [pt]

theorem frame_subst_ev_pt {C : Type} [CommRing C] {d n : ℕ} {σ : Type} (b : Fin n)
    {t : Fin n × Fin d → MvPowerSeries σ C} (ht : HasSubst t) (f : PS C 1 d) :
    subst t (ev ![pt C d b] f) = subst (fun p : Fin 1 × Fin d => t (b, p.2)) f := by
  rw [frame_subst_ev _ (frame_cc_pt b) ht]
  congr 1
  funext p
  simp only [Matrix.cons_val_fin_one, pt]
  exact subst_X ht _

theorem frame_exp_zero {C : Type} [CommRing C] [Algebra ℚ C] {σ : Type} :
    PowerSeries.subst (0 : MvPowerSeries σ C) (PowerSeries.exp C) = 1 := by
  classical
  unfold PowerSeries.subst
  have e : (fun _ : Unit => (0 : MvPowerSeries σ C)) = 0 := rfl
  rw [e, MvPowerSeries.subst_zero_eq_C_constantCoeff]
  ext x
  by_cases hx : x = 0
  · subst hx
    rw [MvPowerSeries.coeff_map, MvPowerSeries.coeff_C, if_pos rfl, MvPowerSeries.coeff_zero_eq_constantCoeff,
      map_one]
    exact PowerSeries.constantCoeff_exp (A := C)
  · rw [MvPowerSeries.coeff_map, MvPowerSeries.coeff_C, if_neg hx, MvPowerSeries.coeff_one, if_neg hx, map_zero]

theorem frameSt_of (hAct : ActSt) (hUnit : UnitSt) : FrameSt := by
  intro C _ _ v d R _ _ O _ _ B hB h hh w0 n
  have hc : constantCoeff h = 0 := GlobalTheory.GaugeBaseChange.const_of_axis hh.ax0
  have hact : ∀ i, constantCoeff (B.actK C w0 i) = 0 := fun i => by
    unfold FB.actK
    rw [constantCoeff_map, B.A.const, map_zero]
  have hpair : ∀ j i, constantCoeff
      ((![pt C d 0, comp1 (B.actK C w0) (pt C d 0)] : Fin 2 → Pt C 1 d) j i) = 0 := by
    intro j i
    fin_cases j
    · simp [pt]
    · exact frame_cc_ev _ (frame_cc_pt 0) (hact i)
  have hcL : constantCoeff (B.hL C h w0) = 0 := frame_cc_ev _ hpair hc
  have hS : constantCoeff (∑ b : Fin n, ev (n := n) ![pt C d b] (B.hL C h w0)) = 0 := by
    rw [map_sum]
    exact Finset.sum_eq_zero fun b _ => frame_cc_ev _ (frame_cc_pt b) hcL
  obtain ⟨-, -, -, hadd, hone, -⟩ := hUnit C v (Fin n × Fin d)
  refine ⟨hone _ hS, fun k => ?_, fun σ _ y hy => ?_⟩
  · unfold frameSer FB.expS
    induction k with
    | zero => rw [Nat.cast_zero, zero_smul, pow_zero, frame_exp_zero]
    | succ k ih =>
      rw [Nat.cast_succ, add_smul, one_smul, hadd _ _ _ hS, ih, pow_succ]
      rw [smul_eq_C_mul, map_mul, hS, mul_zero]
  · have ht : HasSubst (fun q : Fin n × Fin d => expPt (fglOf hB) (y q.1) q.2) :=
      hasSubst_of_constantCoeff_zero fun q => cc_expPt _ (hy q.1) q.2
    have key : subst (fun q : Fin n × Fin d => expPt (fglOf hB) (y q.1) q.2)
        (∑ b : Fin n, ev (n := n) ![pt C d b] (B.hL C h w0)) =
        ∑ j, pairSer (fglOf hB) h (y j) (mv (dAct C B w0) (y j)) := by
      rw [← coe_substAlgHom ht, map_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      have hs : HasSubst (fun p : Fin 1 × Fin d => expPt (fglOf hB) (y b) p.2) :=
        hasSubst_of_constantCoeff_zero fun q => cc_expPt _ (hy b) q.2
      rw [coe_substAlgHom, frame_subst_ev_pt b ht]
      unfold FB.hL pairSer
      rw [frame_subst_ev _ hpair hs, (hAct C v d R O B hB σ w0).1 (y b) (hy b)]
      congr 1
      funext ⟨j, i⟩
      fin_cases j
      · exact subst_X hs _
      · exact frame_subst_ev_pt 0 hs _
    rw [← key]
    unfold frameSer FB.expS PowerSeries.subst
    exact subst_comp_subst_apply (hasSubst_of_constantCoeff_zero fun _ => hS) ht _

end GlobalTheory.IsoTriv
