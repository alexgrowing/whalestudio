import Formalism.LocalToGlobal.CharacterGerms.ValuationEqPairOfBiadditiveCross

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj

namespace VP

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {τ : Type}

variable (Y : FBChart C V O dd)

section Three

variable {a b c : Fin dd → MvPowerSeries τ C} (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0)
  (hb : ∀ i, MvPowerSeries.constantCoeff (b i) = 0) (hc : ∀ i, MvPowerSeries.constantCoeff (c i) = 0)

include ha hb hc

theorem first_partial_law_at_points : MvPowerSeries.subst (P3 a b c) Y.B.ph1 =
    mvExp (hAt Y a c + hAt Y b c - hAt Y (addAt Y a b) c) := by
  have h := Y.gauge.ph1
  rw [toK_eq, eval_two_points_eq_subst _ _ _ rfl, eval_two_points_eq_subst _ _ _ rfl, eval_two_points_eq_subst _ _ _ rfl, addOf_eq] at h
  have k0 := cc_pt (C := C) (dd := dd) (0 : Fin 3)
  have k1 := cc_pt (C := C) (dd := dd) (1 : Fin 3)
  have k2 := cc_pt (C := C) (dd := dd) (2 : Fin 3)
  have hcc : MvPowerSeries.constantCoeff (hAt Y (pt C dd (0 : Fin 3)) (pt C dd (2 : Fin 3)) +
      hAt Y (pt C dd (1 : Fin 3)) (pt C dd (2 : Fin 3)) -
      hAt Y (addAt Y (pt C dd (0 : Fin 3)) (pt C dd (1 : Fin 3))) (pt C dd (2 : Fin 3))) = 0 := by
    rw [map_sub, map_add, cc_hAt Y k0 k2, cc_hAt Y k1 k2, cc_hAt Y (cc_addAt Y k0 k1) k2]
    simp
  have h' : Y.B.ph1 = FB.expS C (hAt Y (pt C dd (0 : Fin 3)) (pt C dd (2 : Fin 3)) +
      hAt Y (pt C dd (1 : Fin 3)) (pt C dd (2 : Fin 3)) -
      hAt Y (addAt Y (pt C dd (0 : Fin 3)) (pt C dd (1 : Fin 3))) (pt C dd (2 : Fin 3))) := h
  have hP := constantCoeff_triple_substitution ha hb hc
  rw [h', expS_eq _ hcc, subst_exp hP hcc, subst_sub' hP, subst_add' hP, hAt_subst Y hP k0 k2, hAt_subst Y hP k1 k2,
    hAt_subst Y hP (cc_addAt Y k0 k1) k2, triple_subst_first_coordinate ha hb hc, triple_subst_second_coordinate ha hb hc, triple_subst_third_coordinate ha hb hc]
  congr 3
  funext i
  rw [addAt_subst Y hP k0 k1, triple_subst_first_coordinate ha hb hc, triple_subst_second_coordinate ha hb hc]

end Three

theorem hAt_zero_left {c : Fin dd → MvPowerSeries τ C} (hc : ∀ i, MvPowerSeries.constantCoeff (c i) = 0) :
    hAt Y (fun _ => 0) c = 0 := by
  have hA : MvPowerSeries.HasSubst (fun q : Fin 1 × Fin dd => c q.2) := by
    first
      | exact MvPowerSeries.HasSubst.of_constantCoeff_zero' (fun q => hc q.2)
      | exact MvPowerSeries.HasSubst.of_constantCoeff_nilpotent
          (fun q => by rw [hc q.2]; exact IsNilpotent.zero)
      | exact ⟨fun q => by rw [hc q.2]; exact IsNilpotent.zero,
          by first
            | exact fun d => Set.toFinite _
            | (simp only [Set.finite_coe_iff]; intro d; exact Set.toFinite _)
            | (simp; intro d; exact Set.toFinite _)⟩
  have h1 : MvPowerSeries.subst (P2 (0 : Pt C 1 dd) (pt C dd 0)) Y.h = 0 := by
    rw [← eval_two_points_eq_subst (m := 2) _ _ _ rfl]
    exact Y.gauge.ax0
  have h3 : hAt Y (fun _ => 0) c =
      MvPowerSeries.subst (fun q : Fin 1 × Fin dd => c q.2) (MvPowerSeries.subst (P2 (0 : Pt C 1 dd) (pt C dd 0)) Y.h) := by
    rw [subst_pair_substitution_comm]
    · unfold hAt
      congr 2
      · funext i
        rw [Pi.zero_apply, ← MvPowerSeries.coe_substAlgHom hA, map_zero]
      · funext i
        first
          | simp [pt, MvPowerSeries.subst_X hA]
          | (unfold pt; simp [MvPowerSeries.subst_X hA])
          | rfl
    all_goals first
      | exact hA
      | (intro i; simp [pt])
      | (intro i; rfl)
      | simp_all
      | skip
  rw [h3, h1, ← MvPowerSeries.coe_substAlgHom hA, map_zero]

theorem hAt_zero_right {c : Fin dd → MvPowerSeries τ C} (hc : ∀ i, MvPowerSeries.constantCoeff (c i) = 0) :
    hAt Y c (fun _ => 0) = 0 := by
  have hA : MvPowerSeries.HasSubst (fun q : Fin 1 × Fin dd => c q.2) := by
    first
      | exact MvPowerSeries.HasSubst.of_constantCoeff_zero' (fun q => hc q.2)
      | exact MvPowerSeries.HasSubst.of_constantCoeff_nilpotent
          (fun q => by rw [hc q.2]; exact IsNilpotent.zero)
      | exact ⟨fun q => by rw [hc q.2]; exact IsNilpotent.zero,
          by first
            | exact fun d => Set.toFinite _
            | (simp only [Set.finite_coe_iff]; intro d; exact Set.toFinite _)
            | (simp; intro d; exact Set.toFinite _)⟩
  have h1 : MvPowerSeries.subst (P2 (pt C dd 0) (0 : Pt C 1 dd)) Y.h = 0 := by
    rw [← eval_two_points_eq_subst (m := 2) _ _ _ rfl]
    exact Y.gauge.ax1
  have h3 : hAt Y c (fun _ => 0) =
      MvPowerSeries.subst (fun q : Fin 1 × Fin dd => c q.2) (MvPowerSeries.subst (P2 (pt C dd 0) (0 : Pt C 1 dd)) Y.h) := by
    rw [subst_pair_substitution_comm]
    · unfold hAt
      congr 2
      · funext i
        first
          | simp [pt, MvPowerSeries.subst_X hA]
          | (unfold pt; simp [MvPowerSeries.subst_X hA])
          | rfl
      · funext i
        rw [Pi.zero_apply, ← MvPowerSeries.coe_substAlgHom hA, map_zero]
    all_goals first
      | exact hA
      | (intro i; simp [pt])
      | (intro i; rfl)
      | simp_all
      | skip
  rw [h3, h1, ← MvPowerSeries.coe_substAlgHom hA, map_zero]

def GoodPt (V : VF C) (a : Fin dd → MvPowerSeries τ C) : Prop :=
  (∀ i, MvPowerSeries.constantCoeff (a i) = 0) ∧ ∀ i, IntS V (a i)

private theorem intS_subst_of_intS {σ : Type} [Finite σ] {a : σ → MvPowerSeries τ C}
    (ha0 : ∀ s, MvPowerSeries.constantCoeff (a s) = 0) (ha : ∀ s, IntS V (a s)) {f : MvPowerSeries σ C}
    (hf : IntS V f) : IntS V (MvPowerSeries.subst a f) := by
  first
    | exact IntS.subst ha0 ha hf
    | exact PartialDerivEval.intS_subst ha0 ha hf
    | exact AltInv.intS_subst ha0 ha hf

theorem GoodPt.add {a b : Fin dd → MvPowerSeries τ C} (ha : GoodPt V a) (hb : GoodPt V b) : GoodPt V (addAt Y a b) := by
  have h0 : ∀ q, MvPowerSeries.constantCoeff (P2 a b q) = 0 := by
    intro q
    unfold P2
    split_ifs
    · exact ha.1 _
    · exact hb.1 _
  have hI : ∀ q, IntS V (P2 a b q) := by
    intro q
    unfold P2
    split_ifs
    · exact ha.2 _
    · exact hb.2 _
  refine ⟨fun i => cc_addAt Y ha.1 hb.1 i, fun i => ?_⟩
  show IntS V (MvPowerSeries.subst (P2 a b) (Y.B.G.F i))
  exact intS_subst_of_intS h0 hI (Y.intF i)

theorem GoodPt.zero : GoodPt V (fun _ : Fin dd => (0 : MvPowerSeries τ C)) := by
  refine ⟨fun _ => map_zero _, fun _ => ?_⟩
  unfold IntS
  intro μ
  rw [map_zero]
  unfold VF.Ge
  first
    | simp
    | exact le_top
    | (simp [VF.v]; done)

theorem GoodPt.act (x : O) {a : Fin dd → MvPowerSeries τ C} (ha : GoodPt V a) : GoodPt V (actAt Y x a) := by
  refine ⟨fun i => cc_actAt Y x ha.1 i, fun i => ?_⟩
  show IntS V (MvPowerSeries.subst (fun q : Fin 1 × Fin dd => a q.2) (Y.B.A.act x i))
  exact intS_subst_of_intS (a := fun q : Fin 1 × Fin dd => a q.2) (fun q => ha.1 q.2) (fun q => ha.2 q.2)
    (Y.intAct x i)

def sumL : List (Fin dd → MvPowerSeries τ C) → (Fin dd → MvPowerSeries τ C)
  | [] => fun _ => 0
  | a :: l => addAt Y a (sumL l)

theorem good_sumL : ∀ l : List (Fin dd → MvPowerSeries τ C), (∀ a ∈ l, GoodPt V a) → GoodPt V (sumL Y l)
  | [], _ => GoodPt.zero
  | a :: l, h => (h a List.mem_cons_self).add Y (good_sumL l fun b hb => h b (List.mem_cons_of_mem _ hb))

theorem isIU_of_exp {U f : MvPowerSeries τ C} (hi : IntS V U) (he : U = mvExp f) : IsIU V U := by
  refine ⟨hi, ?_⟩
  subst he
  unfold mvExp
  have h1 : (MvPowerSeries.constantCoeff fun m : τ →₀ ℕ =>
      ∑ k ∈ Finset.range (Finsupp.degree m + 1), (MvPowerSeries.coeff m) (f ^ k) / (k.factorial : C)) = 1 := by
    show (∑ k ∈ Finset.range (Finsupp.degree (0 : τ →₀ ℕ) + 1),
      (MvPowerSeries.coeff (0 : τ →₀ ℕ)) (f ^ k) / (k.factorial : C)) = 1
    simp
  rw [h1]
  first
    | simp
    | exact map_one _
    | rfl
    | (simp [VF.v]; done)

private theorem mvExp_add_character_germs {σ : Type} {f g : MvPowerSeries σ C} (hf : MvPowerSeries.constantCoeff f = 0)
    (hg : MvPowerSeries.constantCoeff g = 0) : mvExp (f + g) = mvExp f * mvExp g := by
  first
    | exact exp_add hf hg
    | exact Formalism.L2.FormalSeriesBounds.UnitSeriesProduct.mvExp_add' hf hg
    | exact Formalism.IncomingBounds.mvExp_add hf hg
    | exact Formalism.IncomingBounds.mvExp_add' hf hg
    | exact mvExp_add hf hg

private theorem mvExp_zero_eq_one {σ : Type} : mvExp (0 : MvPowerSeries σ C) = 1 := by
  ext m
  show (∑ k ∈ Finset.range (Finsupp.degree m + 1),
    (MvPowerSeries.coeff m) ((0 : MvPowerSeries σ C) ^ k) / (k.factorial : C)) = MvPowerSeries.coeff m 1
  rw [Finset.sum_range_succ']
  simp

theorem biadd_left {c : Fin dd → MvPowerSeries τ C} (hc : GoodPt V c) :
    ∀ l : List (Fin dd → MvPowerSeries τ C), (∀ a ∈ l, GoodPt V a) →
      ∃ U : MvPowerSeries τ C, IsIU V U ∧ mvExp (hAt Y (sumL Y l) c) * U = (l.map fun a => mvExp (hAt Y a c)).prod
  | [], _ => ⟨1, IsIU.one, by
      show mvExp (hAt Y (fun _ => 0) c) * 1 = 1
      rw [hAt_zero_left Y hc.1, rtj_mvExp_zero, one_mul]⟩
  | a :: l, h => by
      have ha := h a List.mem_cons_self
      have hl := good_sumL Y l fun b hb => h b (List.mem_cons_of_mem _ hb)
      obtain ⟨U, hU, e⟩ := biadd_left hc l fun b hb => h b (List.mem_cons_of_mem _ hb)
      have hp := first_partial_law_at_points Y ha.1 hl.1 hc.1
      have hpi : IntS V (MvPowerSeries.subst (P3 a (sumL Y l) c) Y.B.ph1) :=
        IntS.subst (constantCoeff_triple_substitution ha.1 hl.1 hc.1) (integral_triple_substitution ha.2 hl.2 hc.2) Y.intPh1
      refine ⟨MvPowerSeries.subst (P3 a (sumL Y l) c) Y.B.ph1 * U, (isIU_of_exp hpi hp).mul hU, ?_⟩
      have c1 := cc_hAt Y ha.1 hc.1
      have c2 := cc_hAt Y hl.1 hc.1
      have c3 := cc_hAt Y (cc_addAt Y ha.1 hl.1) hc.1
      have e2 : mvExp (hAt Y (addAt Y a (sumL Y l)) c) * MvPowerSeries.subst (P3 a (sumL Y l) c) Y.B.ph1 =
          mvExp (hAt Y a c) * mvExp (hAt Y (sumL Y l) c) := by
        rw [hp, ← exp_add c3 (by rw [map_sub, map_add, c1, c2, c3]; simp), ← exp_add c1 c2]
        congr 1
        ring
      show mvExp (hAt Y (addAt Y a (sumL Y l)) c) * _ = _
      rw [List.map_cons, List.prod_cons, ← e, ← mul_assoc, e2, mul_assoc]

theorem biadd_right {c : Fin dd → MvPowerSeries τ C} (hc : GoodPt V c) :
    ∀ l : List (Fin dd → MvPowerSeries τ C), (∀ a ∈ l, GoodPt V a) →
      ∃ U : MvPowerSeries τ C, IsIU V U ∧ mvExp (hAt Y c (sumL Y l)) * U = (l.map fun a => mvExp (hAt Y c a)).prod
  | [], _ => ⟨1, IsIU.one, by
      show mvExp (hAt Y c (fun _ => 0)) * 1 = 1
      rw [hAt_zero_right Y hc.1, rtj_mvExp_zero, one_mul]⟩
  | a :: l, h => by
      have ha := h a List.mem_cons_self
      have hl := good_sumL Y l fun b hb => h b (List.mem_cons_of_mem _ hb)
      obtain ⟨U, hU, e⟩ := biadd_right hc l fun b hb => h b (List.mem_cons_of_mem _ hb)
      have hp := second_partial_law_at_points Y hc.1 ha.1 hl.1
      have hpi : IntS V (MvPowerSeries.subst (P3 c a (sumL Y l)) Y.B.ph2) :=
        IntS.subst (constantCoeff_triple_substitution hc.1 ha.1 hl.1) (integral_triple_substitution hc.2 ha.2 hl.2) Y.intPh2
      refine ⟨MvPowerSeries.subst (P3 c a (sumL Y l)) Y.B.ph2 * U, (isIU_of_exp hpi hp).mul hU, ?_⟩
      have c1 := cc_hAt Y hc.1 ha.1
      have c2 := cc_hAt Y hc.1 hl.1
      have c3 := cc_hAt Y hc.1 (cc_addAt Y ha.1 hl.1)
      have e2 : mvExp (hAt Y c (addAt Y a (sumL Y l))) * MvPowerSeries.subst (P3 c a (sumL Y l)) Y.B.ph2 =
          mvExp (hAt Y c a) * mvExp (hAt Y c (sumL Y l)) := by
        rw [hp, ← exp_add c3 (by rw [map_sub, map_add, c1, c2, c3]; simp), ← exp_add c1 c2]
        congr 1
        ring
      show mvExp (hAt Y c (addAt Y a (sumL Y l))) * _ = _
      rw [List.map_cons, List.prod_cons, ← e, ← mul_assoc, e2, mul_assoc]

end VP

end Formalism.L2.FormalSeriesBounds
