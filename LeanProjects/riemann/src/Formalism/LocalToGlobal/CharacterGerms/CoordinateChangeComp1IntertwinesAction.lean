import Formalism.LocalToGlobal.CharacterGerms.FirstPartialLawAtPoints

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj

namespace VP

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {τ : Type}

variable (Y : FBChart C V O dd)

theorem coordinateChange_comp1_intertwines_action {n : ℕ} (x : O) (a : Pt C n dd) : comp1 (Y.B.A.act x) a = actAt Y x a := by
  unfold actAt
  unfold comp1
  funext i
  unfold ev
  first
  | rfl
  | (congr 1; funext q; simp)
  | (congr 1; funext q; skip)

theorem addOf_eq' {n : ℕ} (a b : Pt C n dd) : addOf Y.B.G.F a b = addAt Y a b := by
  unfold addAt
  unfold addOf
  funext i
  unfold ev
  first
  | rfl
  | (congr 1; funext q; unfold P2; rfl)
  | (congr 1; funext q; unfold P2; obtain ⟨j, k⟩ := q; fin_cases j <;> simp)

theorem actAt_addAt (x : O) {a b : Fin dd → MvPowerSeries τ C} (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0)
    (hb : ∀ i, MvPowerSeries.constantCoeff (b i) = 0) :
    actAt Y x (addAt Y a b) = addAt Y (actAt Y x a) (actAt Y x b) := by
  have h := Y.B.A.hom x
  rw [show Y.B.G.add (pt C (n := 2) dd 0) (pt C (n := 2) dd 1) = addAt Y (pt C dd 0) (pt C dd 1) from addOf_eq' Y _ _,
    show Y.B.G.add (comp1 (Y.B.A.act x) (pt C (n := 2) dd 0)) (comp1 (Y.B.A.act x) (pt C (n := 2) dd 1)) =
      addAt Y (comp1 (Y.B.A.act x) (pt C dd 0)) (comp1 (Y.B.A.act x) (pt C dd 1)) from addOf_eq' Y _ _,
    coordinateChange_comp1_intertwines_action, coordinateChange_comp1_intertwines_action, coordinateChange_comp1_intertwines_action] at h
  have k0 := cc_pt (C := C) (dd := dd) (0 : Fin 2)
  have k1 := cc_pt (C := C) (dd := dd) (1 : Fin 2)
  have hP := constantCoeff_pair_substitution ha hb
  have e0 : (fun i => MvPowerSeries.subst (P2 a b) (pt C dd (0 : Fin 2) i)) = a := funext fun i => pair_subst_coordinate ha hb 0 i
  have e1 : (fun i => MvPowerSeries.subst (P2 a b) (pt C dd (1 : Fin 2) i)) = b := funext fun i => pair_subst_coordinate ha hb 1 i
  funext i
  have h2 := congrArg (MvPowerSeries.subst (P2 a b)) (congrFun h i)
  rw [actAt_subst Y hP (cc_addAt Y k0 k1), addAt_subst Y hP (cc_actAt Y x k0) (cc_actAt Y x k1)] at h2
  have e2 : (fun i => MvPowerSeries.subst (P2 a b) (addAt Y (pt C dd (0 : Fin 2)) (pt C dd (1 : Fin 2)) i)) =
      addAt Y a b := by
    funext j
    rw [addAt_subst Y hP k0 k1, e0, e1]
  have e3 : (fun i => MvPowerSeries.subst (P2 a b) (actAt Y x (pt C dd (0 : Fin 2)) i)) = actAt Y x a := by
    funext j
    rw [actAt_subst Y hP k0, e0]
  have e4 : (fun i => MvPowerSeries.subst (P2 a b) (actAt Y x (pt C dd (1 : Fin 2)) i)) = actAt Y x b := by
    funext j
    rw [actAt_subst Y hP k1, e1]
  rw [e2, e3, e4] at h2
  exact h2

theorem actAt_zero (x : O) : actAt Y x (fun _ : Fin dd => (0 : MvPowerSeries τ C)) = fun _ => 0 := by
  funext i
  unfold actAt
  rw [subst_zeroPt, Y.B.A.const, map_zero]

theorem actAt_sumL (x : O) : ∀ l : List (Fin dd → MvPowerSeries τ C), (∀ a ∈ l, GoodPt V a) →
    actAt Y x (sumL Y l) = sumL Y (l.map (actAt Y x))
  | [], _ => actAt_zero Y x
  | a :: l, h => by
      show actAt Y x (addAt Y a (sumL Y l)) = addAt Y (actAt Y x a) (sumL Y (l.map (actAt Y x)))
      rw [actAt_addAt Y x (h a List.mem_cons_self).1
        (good_sumL Y l fun b hb => h b (List.mem_cons_of_mem _ hb)).1,
        actAt_sumL x l fun b hb => h b (List.mem_cons_of_mem _ hb)]

theorem biadd_right_list (l2 : List (Fin dd → MvPowerSeries τ C)) (h2 : ∀ a ∈ l2, GoodPt V a) :
    ∀ l1 : List (Fin dd → MvPowerSeries τ C), (∀ a ∈ l1, GoodPt V a) →
      ∃ U : MvPowerSeries τ C, IsIU V U ∧ (l1.map fun a => mvExp (hAt Y a (sumL Y l2))).prod * U =
        (l1.map fun a => (l2.map fun b => mvExp (hAt Y a b)).prod).prod
  | [], _ => ⟨1, IsIU.one, by simp⟩
  | a :: l1, h => by
      obtain ⟨U, hU, e⟩ := biadd_right_list l2 h2 l1 fun b hb => h b (List.mem_cons_of_mem _ hb)
      obtain ⟨U', hU', e'⟩ := biadd_right Y (h a List.mem_cons_self) l2 h2
      refine ⟨U' * U, hU'.mul hU, ?_⟩
      rw [List.map_cons, List.prod_cons, List.map_cons, List.prod_cons, ← e, ← e']
      ring

theorem biadd_both (x : O) (l : List (Fin dd → MvPowerSeries τ C)) (h : ∀ a ∈ l, GoodPt V a) :
    ∃ U : MvPowerSeries τ C, IsIU V U ∧ mvExp (hAt Y (sumL Y l) (actAt Y x (sumL Y l))) * U =
      (l.map fun a => (l.map fun b => mvExp (hAt Y a (actAt Y x b))).prod).prod := by
  have hx : ∀ a ∈ l.map (actAt Y x), GoodPt V a := by
    intro a ha
    obtain ⟨b, hb, rfl⟩ := List.mem_map.1 ha
    exact (h b hb).act Y x
  obtain ⟨U, hU, e⟩ := biadd_left Y (good_sumL Y _ hx) l h
  obtain ⟨U', hU', e'⟩ := biadd_right_list Y (l.map (actAt Y x)) hx l h
  refine ⟨U * U', hU.mul hU', ?_⟩
  rw [actAt_sumL Y x l h, ← mul_assoc, e, e']
  simp only [List.map_map]
  rfl

end VP

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {d : ℕ} [NeZero d]
  {Orb : Type} [Fintype Orb] {I : Orb → Fin 2 → Type} [∀ o g, Fintype (I o g)]

def projList (π : Orb → Fin 2 → Fin dd → PS C 1 dd) : List (Fin dd → PS C 1 dd) :=
  (Finset.univ : Finset (Orb × Fin 2)).toList.map fun s => π s.1 s.2

def SumProjSt (Y : FBChart C V O dd) (p : ∀ o, PairData Y d (I o)) : Prop :=
  PairsSep Y p → ∀ π, IsProj Y p π → ∀ i, pull1 Y p (pt C dd (0 : Fin 1) i) = pull1 Y p (VP.sumL Y (projList π) i)

theorem biadd_of_sum (Y : FBChart C V O dd) (p : ∀ o, PairData Y d (I o)) (hS : SumProjSt Y p) : BiaddSt Y p := by
  intro hs π hπ
  have hgood : ∀ a ∈ projList π, VP.GoodPt V a := by
    intro a ha
    obtain ⟨s, -, rfl⟩ := List.mem_map.1 ha
    exact ⟨hπ.cc s.1 s.2, hπ.int s.1 s.2⟩
  have hσ := VP.good_sumL Y _ hgood
  obtain ⟨U, hU, e⟩ := VP.biadd_both Y Y.w0 (projList π) hgood
  obtain ⟨U', hU'i, hUU⟩ := VP.intInv (hU.1.pow Y.k) (by rw [map_pow, V.v.map_pow, hU.2, smul_zero])
  have hU'0 : V.v (MvPowerSeries.constantCoeff U') = 0 := by
    have h1 := congrArg (fun x => V.v (MvPowerSeries.constantCoeff x)) hUU
    simp only [map_mul, map_pow, map_one, V.v.map_mul, V.v.map_pow, V.v.map_one, hU.2, smul_zero, add_zero] at h1
    exact h1
  refine ⟨U', ⟨hU'i, hU'0⟩, ?_⟩
  set σ := VP.sumL Y (projList π) with hσd
  have cσ := VP.cc_hAt Y hσ.1 (VP.cc_actAt Y Y.w0 hσ.1)

  have e1 : mvExp ((Y.k : C) • VP.hAt Y σ (VP.actAt Y Y.w0 σ)) =
      U' * ∏ s : Orb × Fin 2, ∏ s' : Orb × Fin 2, Aterm Y π s s' := by
    have e2 : (∏ s : Orb × Fin 2, ∏ s' : Orb × Fin 2, Aterm Y π s s') =
        (mvExp (VP.hAt Y σ (VP.actAt Y Y.w0 σ)) * U) ^ Y.k := by
      rw [e]
      unfold projList
      simp only [List.map_map]
      rw [Finset.prod_map_toList, ← Finset.prod_pow]
      refine Finset.prod_congr rfl fun s _ => ?_
      show _ = ((((Finset.univ : Finset (Orb × Fin 2)).toList.map _).prod) ^ Y.k)
      rw [Finset.prod_map_toList, ← Finset.prod_pow]
      refine Finset.prod_congr rfl fun s' _ => ?_
      rw [VP.Aterm_eq Y π hπ.cc, VP.exp_nsmul (VP.cc_hAt Y (hπ.cc _ _) (VP.cc_actAt Y _ (hπ.cc _ _)))]
      rfl
    rw [e2, mul_pow, ← VP.exp_nsmul cσ]
    calc mvExp ((Y.k : C) • VP.hAt Y σ (VP.actAt Y Y.w0 σ))
        = (U' * U ^ Y.k) * mvExp ((Y.k : C) • VP.hAt Y σ (VP.actAt Y Y.w0 σ)) := by rw [hUU, one_mul]
      _ = U' * (mvExp ((Y.k : C) • VP.hAt Y σ (VP.actAt Y Y.w0 σ)) * U ^ Y.k) := by ring

  have hA := VP.cc_pull1Pt Y p
  have k0 := VP.cc_pt (C := C) (dd := dd) (0 : Fin 1)
  have hLeq : Y.B.hL C Y.h Y.w0 = VP.hAt Y (pt C dd (0 : Fin 1)) (VP.actAt Y Y.w0 (pt C dd (0 : Fin 1))) := by
    unfold FB.hL
    rw [VP.eval_two_points_eq_subst _ _ _ rfl, VP.compose_one_action_eq_actAt]
    rfl
  have hpt : (fun i => MvPowerSeries.subst (fun q : Fin 1 × Fin dd => expAll Y p q.2) (pt C dd (0 : Fin 1) i)) =
      fun i => MvPowerSeries.subst (fun q : Fin 1 × Fin dd => expAll Y p q.2) (σ i) := funext fun i => hS hs π hπ i
  have e3 : pull1 Y p (FB.expS C ((Y.k : C) • Y.B.hL C Y.h Y.w0)) =
      pull1 Y p (mvExp ((Y.k : C) • VP.hAt Y σ (VP.actAt Y Y.w0 σ))) := by
    rw [VP.expS_eq _ (VP.cc_smul _ (VP.cc_hL Y)), hLeq]
    unfold pull1
    rw [VP.subst_exp hA (VP.cc_smul _ (VP.cc_hAt Y k0 (VP.cc_actAt Y _ k0))), VP.subst_exp hA (VP.cc_smul _ cσ),
      VP.subst_smul hA, VP.subst_smul hA, VP.hAt_subst Y hA k0 (VP.cc_actAt Y _ k0),
      VP.hAt_subst Y hA hσ.1 (VP.cc_actAt Y _ hσ.1)]
    have a1 : (fun i => MvPowerSeries.subst (fun q : Fin 1 × Fin dd => expAll Y p q.2)
        (VP.actAt Y Y.w0 (pt C dd (0 : Fin 1)) i)) =
        fun i => MvPowerSeries.subst (fun q : Fin 1 × Fin dd => expAll Y p q.2) (VP.actAt Y Y.w0 σ i) := by
      funext i
      rw [VP.actAt_subst Y hA k0, VP.actAt_subst Y hA hσ.1, hpt]
    rw [a1, hpt]
  rw [e3, e1, VP.pullback_one_var_mul, VP.pullback_one_var_prod]
  congr 1
  exact Finset.prod_congr rfl fun s _ => VP.pullback_one_var_prod Y p _ _

end Formalism.L2.FormalSeriesBounds
