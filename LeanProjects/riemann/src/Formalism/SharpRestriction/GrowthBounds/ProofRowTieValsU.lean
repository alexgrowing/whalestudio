import Formalism.SharpRestriction.GrowthBounds.ProofRowTieValsE

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj

namespace VS

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {d : ℕ} [NeZero d]
  {Orb : Type} [Fintype Orb] {I0 : Orb → Type} [∀ o, Fintype (I0 o)]

theorem exp_sum {σ ι : Type} (s : Finset ι) {f : ι → MvPowerSeries σ C}
    (h : ∀ i ∈ s, MvPowerSeries.constantCoeff (f i) = 0) : mvExp (∑ i ∈ s, f i) = ∏ i ∈ s, mvExp (f i) := by
  classical
  revert h
  refine Finset.induction_on s ?_ ?_
  · intro _
    simp only [Finset.sum_empty, Finset.prod_empty]
    ext m
    rw [MvPowerSeries.coeff_one]
    change ∑ k ∈ Finset.range (m.degree + 1),
      MvPowerSeries.coeff m ((0 : MvPowerSeries σ C) ^ k) / (k.factorial : C) = _
    rw [Finset.sum_range_succ']
    simp [MvPowerSeries.coeff_one]
  · intro a t ha ih h
    have ht : ∀ i ∈ t, MvPowerSeries.constantCoeff (f i) = 0 := fun i hi => h i (Finset.mem_insert_of_mem hi)
    rw [Finset.sum_insert ha, Finset.prod_insert ha, VP.exp_add (h a (Finset.mem_insert_self a t)), ih ht]
    rw [map_sum]
    exact Finset.sum_eq_zero ht

variable (Y : FBChart C V O dd) (p : ∀ o, SelfData Y d (I0 o))

theorem HK_zeroR (κ : WVO (IS I0) → C) : HK Y p κ 0 = 0 := by
  show VP.hAt Y (EK Y p κ) (EK Y p 0) = 0
  rw [EK_zero]
  exact VP.hAt_zero_right (Y := Y) (cc_EK Y p κ)

theorem HK_zeroL (κ : WVO (IS I0) → C) : HK Y p 0 κ = 0 := by
  show VP.hAt Y (EK Y p 0) (EK Y p κ) = 0
  rw [EK_zero]
  exact VP.hAt_zero_left (Y := Y) (cc_EK Y p κ)

theorem HK_addL {κ₁ κ₂ κ' : WVO (IS I0) → C} (h₁ : GK Y p κ₁) (h₂ : GK Y p κ₂) (h' : GK Y p κ') :
    Cg V (AA Y p) (HK Y p (κ₁ + κ₂) κ') (HK Y p κ₁ κ' + HK Y p κ₂ κ') := by
  have e := gauge_congr_additive_left (Y := Y) (cc_AA Y p) h₁ h₂ h'
  rw [EK_add] at e
  exact e

theorem HK_addR {κ κ₁ κ₂ : WVO (IS I0) → C} (h : GK Y p κ) (h₁ : GK Y p κ₁) (h₂ : GK Y p κ₂) :
    Cg V (AA Y p) (HK Y p κ (κ₁ + κ₂)) (HK Y p κ κ₁ + HK Y p κ κ₂) := by
  have e := gauge_congr_additive_right (Y := Y) (cc_AA Y p) h h₁ h₂
  rw [EK_add] at e
  exact e

theorem HK_sumL {ι : Type} (s : Finset ι) {κ : ι → WVO (IS I0) → C} (h : ∀ i ∈ s, GK Y p (κ i))
    {κ' : WVO (IS I0) → C} (h' : GK Y p κ') :
    Cg V (AA Y p) (HK Y p (∑ i ∈ s, κ i) κ') (∑ i ∈ s, HK Y p (κ i) κ') := by
  classical
  have hG : ∀ t : Finset ι, (∀ i ∈ t, GK Y p (κ i)) → GK Y p (∑ i ∈ t, κ i) := by
    intro t
    refine Finset.induction_on t ?_ ?_
    · intro _
      show GImg V (AA Y p) (EK Y p (∑ i ∈ (∅ : Finset ι), κ i))
      rw [Finset.sum_empty, EK_zero]
      exact GImg.zero (cc_AA Y p)
    · intro a t ha ih ht
      show GImg V (AA Y p) (EK Y p (∑ i ∈ insert a t, κ i))
      rw [Finset.sum_insert ha, ← EK_add]
      exact GImg.add (Y := Y) (cc_AA Y p) (ht a (Finset.mem_insert_self a t))
        (ih fun i hi => ht i (Finset.mem_insert_of_mem hi))
  revert h
  refine Finset.induction_on s ?_ ?_
  · intro _
    simp only [Finset.sum_empty]
    rw [HK_zeroL]
    exact Cg.refl (cc_AA Y p) (map_zero _)
  · intro a t ha ih h
    have ht : ∀ i ∈ t, GK Y p (κ i) := fun i hi => h i (Finset.mem_insert_of_mem hi)
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact Cg.trans (cc_AA Y p) (HK_addL Y p (h a (Finset.mem_insert_self a t)) (hG t ht) h')
      (Cg.add (cc_AA Y p) (Cg.refl (cc_AA Y p) (cc_HK Y p _ _)) (ih ht))

theorem HK_sumR {ι : Type} (s : Finset ι) {κ : ι → WVO (IS I0) → C} (h : ∀ i ∈ s, GK Y p (κ i))
    {κ' : WVO (IS I0) → C} (h' : GK Y p κ') :
    Cg V (AA Y p) (HK Y p κ' (∑ i ∈ s, κ i)) (∑ i ∈ s, HK Y p κ' (κ i)) := by
  classical
  have hG : ∀ t : Finset ι, (∀ i ∈ t, GK Y p (κ i)) → GK Y p (∑ i ∈ t, κ i) := by
    intro t
    refine Finset.induction_on t ?_ ?_
    · intro _
      show GImg V (AA Y p) (EK Y p (∑ i ∈ (∅ : Finset ι), κ i))
      rw [Finset.sum_empty, EK_zero]
      exact GImg.zero (cc_AA Y p)
    · intro a t ha ih ht
      show GImg V (AA Y p) (EK Y p (∑ i ∈ insert a t, κ i))
      rw [Finset.sum_insert ha, ← EK_add]
      exact GImg.add (Y := Y) (cc_AA Y p) (ht a (Finset.mem_insert_self a t))
        (ih fun i hi => ht i (Finset.mem_insert_of_mem hi))
  revert h
  refine Finset.induction_on s ?_ ?_
  · intro _
    simp only [Finset.sum_empty]
    rw [HK_zeroR]
    exact Cg.refl (cc_AA Y p) (map_zero _)
  · intro a t ha ih h
    have ht : ∀ i ∈ t, GK Y p (κ i) := fun i hi => h i (Finset.mem_insert_of_mem hi)
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact Cg.trans (cc_AA Y p) (HK_addR Y p h' (h a (Finset.mem_insert_self a t)) (hG t ht))
      (Cg.add (cc_AA Y p) (Cg.refl (cc_AA Y p) (cc_HK Y p _ _)) (ih ht))

theorem HK_sy {κ κ' : WVO (IS I0) → C} (h : GK Y p κ) (h' : GK Y p κ') :
    Cg V (AA Y p) (HK Y p κ' κ) (HK Y p κ κ') :=
  cg_sy (Y := Y) (cc_AA Y p) h h'

theorem HK_ad (x : O) {κ κ' : WVO (IS I0) → C} (h : GK Y p κ) (h' : GK Y p κ') :
    Cg V (AA Y p) (HK Y p (lamAct Y p x * κ) κ') (HK Y p κ (lamAct Y p (star x) * κ')) := by
  have e := cg_ad (Y := Y) (cc_AA Y p) x h h'
  simp only [EK_act] at e
  exact e

theorem lamAct_tr : lamAct Y p Y.w0 + lamAct Y p (star Y.w0) = 1 := by
  funext w
  simp only [Pi.add_apply, Pi.one_apply, lamAct]
  rw [← map_add, Y.halfIntegralGenerator_add_conj_eq_one, map_one]

theorem HK_pair {a b : WVO (IS I0) → C} (ha : GK Y p a) (hb : GK Y p b) :
    Cg V (AA Y p) (HK Y p a (lamAct Y p Y.w0 * b) + HK Y p b (lamAct Y p Y.w0 * a)) (HK Y p a b) := by
  have hA := cc_AA Y p
  have e1 : Cg V (AA Y p) (HK Y p b (lamAct Y p Y.w0 * a)) (HK Y p a (lamAct Y p (star Y.w0) * b)) :=
    Cg.trans hA (HK_sy Y p (GK.act Y p Y.w0 ha) hb) (HK_ad Y p Y.w0 ha hb)
  have e3 := HK_addR Y p ha (GK.act Y p Y.w0 hb) (GK.act Y p (star Y.w0) hb)
  have e4 : lamAct Y p Y.w0 * b + lamAct Y p (star Y.w0) * b = b := by
    rw [← add_mul, lamAct_tr, one_mul]
  rw [e4] at e3
  exact Cg.trans hA (Cg.add hA (Cg.refl hA (cc_HK Y p _ _)) e1) (Cg.symm hA e3)

section Pack

variable {Y p} {γ γ' : Orb → Fin 2 → Fin 2 → Pt C 1 dd} (hs : SelfSep Y p) (hG : ∀ o, GmPack Y (p o) (γ o) (γ' o))

include hs hG

theorem HK_adj (o : Orb) (r s : Fin 2) {κ κ' : WVO (IS I0) → C} (h : GK Y p κ) (h' : GK Y p κ') :
    Cg V (AA Y p) (HK Y p (lamG Y p o r s * κ) κ') (HK Y p κ (lamG' Y p o r s * κ')) := by
  have hA := cc_AA Y p
  have e := cg_adj (Y := Y) hA ((hG o).endo r s).cc ((hG o).endo' r s).cc ((hG o).adj r s) h h'
  rw [EK_map Y p ((hG o).endo r s) (diagG hs hG o r s) κ,
    EK_map Y p ((hG o).endo' r s) (diagG' hs hG o r s) κ'] at e
  exact e

theorem HK_key (o o' : Orb) (g g' : Fin 2) {κ κ' : WVO (IS I0) → C} (h : GK Y p κ) (h' : GK Y p κ') :
    Cg V (AA Y p) (∑ col, HK Y p (lamG Y p o col g * κ) (lamG Y p o' col g' * κ'))
      (HK Y p κ (∑ col, lamG' Y p o col g * (lamG Y p o' col g' * κ'))) := by
  have hA := cc_AA Y p
  refine Cg.trans hA (Cg.sum hA Finset.univ fun col _ =>
    HK_adj hs hG o col g h (GK.mulG hs hG o' col g' h')) ?_
  exact Cg.symm hA (HK_sumR Y p Finset.univ
    (fun col _ => GK.mulG' hs hG o col g (GK.mulG hs hG o' col g' h')) h)

theorem HK_gram (o o' : Orb) (g g' : Fin 2) {μ : WVO (IS I0) → C} (hμ : GK Y p (μ * ind (o', g'))) :
    Cg V (AA Y p) (∑ col, HK Y p (lamG Y p o col g * ind (o, g)) (lamG Y p o' col g' * (μ * ind (o', g'))))
      (HK Y p (ind (o, g)) (if (o', g') = (o, 1 - g) then μ * ind (o', g') else 0)) := by
  have e := HK_key hs hG o o' g g' (GK_ind hs hG (o, g)) hμ
  rw [gram_eq] at e
  exact e

theorem main_cg :
    Cg V (AA Y p) (∑ col, HK Y p (kCol Y p col) (lamAct Y p Y.w0 * kCol Y p col))
      (∑ o, ∑ col, HK Y p (lamG Y p o col 0 * ind (o, 0)) (lamG Y p o col 1 * ind (o, 1))) := by
  classical
  have hA := cc_AA Y p
  have ha : ∀ (col : Fin 2) (s : Orb × Fin 2), GK Y p (lamG Y p s.1 col s.2 * ind s) :=
    fun col s => GK.mulG hs hG s.1 col s.2 (GK_ind hs hG s)
  have e1 : ∀ col : Fin 2, Cg V (AA Y p) (HK Y p (kCol Y p col) (lamAct Y p Y.w0 * kCol Y p col))
      (∑ s : Orb × Fin 2, ∑ t : Orb × Fin 2, HK Y p (lamG Y p s.1 col s.2 * ind s)
        (lamG Y p t.1 col t.2 * (lamAct Y p Y.w0 * ind t))) := by
    intro col
    have hK : GK Y p (lamAct Y p Y.w0 * kCol Y p col) := GK.act Y p Y.w0 (GK_col Y p col)
    have hsum := HK_sumL Y p Finset.univ (κ := fun s : Orb × Fin 2 => lamG Y p s.1 col s.2 * ind s)
      (fun s _ => ha col s) hK
    beta_reduce at hsum
    rw [← kCol_eq] at hsum
    refine Cg.trans hA hsum (Cg.sum hA Finset.univ fun s _ => ?_)
    have hR := HK_sumR Y p Finset.univ
      (κ := fun t : Orb × Fin 2 => lamG Y p t.1 col t.2 * (lamAct Y p Y.w0 * ind t))
      (fun t _ => GK.mulG hs hG t.1 col t.2 (GK.act Y p Y.w0 (GK_ind hs hG t))) (ha col s)
    beta_reduce at hR
    have hE : (∑ t : Orb × Fin 2, lamG Y p t.1 col t.2 * (lamAct Y p Y.w0 * ind t)) =
        lamAct Y p Y.w0 * kCol Y p col := by
      rw [kCol_eq, Finset.mul_sum]
      exact Finset.sum_congr rfl fun t _ => by ring
    rw [hE] at hR
    exact hR
  have e2 : Cg V (AA Y p) (∑ col : Fin 2, HK Y p (kCol Y p col) (lamAct Y p Y.w0 * kCol Y p col))
      (∑ s : Orb × Fin 2, ∑ t : Orb × Fin 2,
        HK Y p (ind s) (if t = (s.1, 1 - s.2) then lamAct Y p Y.w0 * ind t else 0)) := by
    refine Cg.trans hA (Cg.sum hA Finset.univ fun col _ => e1 col) ?_
    rw [Finset.sum_comm]
    refine Cg.sum hA Finset.univ fun s _ => ?_
    rw [Finset.sum_comm]
    exact Cg.sum hA Finset.univ fun t _ =>
      HK_gram hs hG s.1 t.1 s.2 t.2 (GK.act Y p Y.w0 (GK_ind hs hG t))
  have e3 : ∀ s : Orb × Fin 2, (∑ t : Orb × Fin 2,
      HK Y p (ind s) (if t = (s.1, 1 - s.2) then lamAct Y p Y.w0 * ind t else 0)) =
      HK Y p (ind s) (lamAct Y p Y.w0 * ind (s.1, 1 - s.2)) := by
    intro s
    simp only [apply_ite (HK Y p (ind s)), HK_zeroR, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have e4 : (∑ s : Orb × Fin 2, HK Y p (ind s) (lamAct Y p Y.w0 * ind (s.1, 1 - s.2))) =
      ∑ o : Orb, (HK Y p (ind (o, 0)) (lamAct Y p Y.w0 * ind (o, 1)) +
        HK Y p (ind (o, 1)) (lamAct Y p Y.w0 * ind (o, 0))) := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun o _ => ?_
    rw [Fin.sum_univ_two]
    simp
  have e5 : Cg V (AA Y p) (∑ o : Orb, (HK Y p (ind (o, 0)) (lamAct Y p Y.w0 * ind (o, 1)) +
      HK Y p (ind (o, 1)) (lamAct Y p Y.w0 * ind (o, 0)))) (∑ o : Orb, HK Y p (ind (o, 0)) (ind (o, 1))) :=
    Cg.sum hA Finset.univ fun o _ => HK_pair Y p (GK_ind hs hG (o, 0)) (GK_ind hs hG (o, 1))
  have e6 : Cg V (AA Y p)
      (∑ o, ∑ col, HK Y p (lamG Y p o col 0 * ind (o, 0)) (lamG Y p o col 1 * ind (o, 1)))
      (∑ o : Orb, HK Y p (ind (o, 0)) (ind (o, 1))) := by
    refine Cg.sum hA Finset.univ fun o _ => ?_
    have hμ : GK Y p (1 * ind (o, 1)) := by rw [one_mul]; exact GK_ind hs hG (o, 1)
    have e := HK_gram hs hG o o 0 1 hμ
    have hc : ((o, (1 : Fin 2)) = (o, 1 - 0)) := by simp
    rw [if_pos hc] at e
    simp only [one_mul] at e
    exact e
  have e23 := e2
  simp only [e3] at e23
  rw [e4] at e23
  exact Cg.trans hA e23 (Cg.trans hA e5 (Cg.symm hA e6))

end Pack

theorem pullback_exp_column (col : Fin 2) :
    pull2 Y p (ev (n := 2) ![pt C dd col] (FB.expS C ((Y.k : C) • Y.B.hL C Y.h Y.w0))) =
      mvExp ((Y.k : C) • HK Y p (kCol Y p col) (lamAct Y p Y.w0 * kCol Y p col)) := by
  have hAA0 : ∀ q : Fin 2 × Fin dd, MvPowerSeries.constantCoeff (VP.linPt Y (uS Y p) q) = 0 :=
    fun q => cc_AA Y p q
  have hAA : MvPowerSeries.HasSubst (VP.linPt Y (uS Y p)) := by
    first
      | exact MvPowerSeries.hasSubst_of_constantCoeff_zero hAA0
      | exact MvPowerSeries.HasSubst.of_constantCoeff_nilpotent fun q => by
          rw [(hAA0) q]; exact IsNilpotent.zero
  have hb0 : ∀ q : Fin 1 × Fin dd, MvPowerSeries.constantCoeff (AA Y p (col, q.2)) = 0 :=
    fun q => cc_AA Y p _
  have hb : MvPowerSeries.HasSubst (fun q : Fin 1 × Fin dd => AA Y p (col, q.2)) := by
    first
      | exact MvPowerSeries.hasSubst_of_constantCoeff_zero hb0
      | exact MvPowerSeries.HasSubst.of_constantCoeff_nilpotent fun q => by
          rw [(hb0) q]; exact IsNilpotent.zero
  have hpc0 : ∀ q : Fin 1 × Fin dd,
      MvPowerSeries.constantCoeff ((![pt C dd col] : Fin 1 → Pt C 2 dd) q.1 q.2) = 0 := by
    rintro ⟨j, i⟩
    fin_cases j
    exact MvPowerSeries.constantCoeff_X _
  have hpc : MvPowerSeries.HasSubst
      (fun q : Fin 1 × Fin dd => (![pt C dd col] : Fin 1 → Pt C 2 dd) q.1 q.2) := by
    first
      | exact MvPowerSeries.hasSubst_of_constantCoeff_zero hpc0
      | exact MvPowerSeries.HasSubst.of_constantCoeff_nilpotent fun q => by
          rw [(hpc0) q]; exact IsNilpotent.zero
  have hp00 : ∀ q : Fin 1 × Fin dd,
      MvPowerSeries.constantCoeff ((![pt C dd 0] : Fin 1 → Pt C 1 dd) q.1 q.2) = 0 := by
    rintro ⟨j, i⟩
    fin_cases j
    exact MvPowerSeries.constantCoeff_X _
  have hp0 : MvPowerSeries.HasSubst
      (fun q : Fin 1 × Fin dd => (![pt C dd 0] : Fin 1 → Pt C 1 dd) q.1 q.2) := by
    first
      | exact MvPowerSeries.hasSubst_of_constantCoeff_zero hp00
      | exact MvPowerSeries.HasSubst.of_constantCoeff_nilpotent fun q => by
          rw [(hp00) q]; exact IsNilpotent.zero
  have hbX : ∀ i : Fin dd, MvPowerSeries.subst (fun q : Fin 1 × Fin dd => AA Y p (col, q.2))
      (MvPowerSeries.X ((0 : Fin 1), i) : MvPowerSeries (Fin 1 × Fin dd) C) = EK Y p (kCol Y p col) i := by
    intro i
    rw [MvPowerSeries.subst_X hb]
    exact AA_eq Y p col i
  have hF : MvPowerSeries.constantCoeff ((Y.k : C) • Y.B.hL C Y.h Y.w0) = 0 := by
    rw [MvPowerSeries.smul_eq_C_mul, map_mul, VP.cc_hL, mul_zero]
  have s1 : pull2 Y p (ev (n := 2) ![pt C dd col] (FB.expS C ((Y.k : C) • Y.B.hL C Y.h Y.w0))) =
      MvPowerSeries.subst (fun q : Fin 1 × Fin dd => AA Y p (col, q.2))
        (FB.expS C ((Y.k : C) • Y.B.hL C Y.h Y.w0)) := by
    unfold pull2 VP.linPull ev
    rw [MvPowerSeries.subst_comp_subst_apply hpc hAA]
    congr 1
    funext q
    rcases q with ⟨j, i⟩
    fin_cases j
    show MvPowerSeries.subst (VP.linPt Y (uS Y p)) (MvPowerSeries.X (col, i)) = _
    rw [MvPowerSeries.subst_X hAA]
    rfl
  rw [s1, VP.expS_eq _ hF, VP.subst_exp hb0 hF]
  congr 1
  rw [← MvPowerSeries.coe_substAlgHom hb, map_smul, MvPowerSeries.coe_substAlgHom]
  congr 1
  unfold FB.hL
  rw [VP.eval_two_points_eq_subst _ _ _ rfl]
  change MvPowerSeries.subst _ (VP.hAt Y (pt C dd 0) (comp1 (Y.B.actK C Y.w0) (pt C dd 0))) = _
  rw [VP.hAt_subst (u := pt C dd 0) (v := comp1 (Y.B.actK C Y.w0) (pt C dd 0)) (hA := hb0)
    (hu := fun i => by exact MvPowerSeries.constantCoeff_X _) (hv := fun i => by
    show MvPowerSeries.constantCoeff (MvPowerSeries.subst
      (fun q : Fin 1 × Fin dd => (![pt C dd 0] : Fin 1 → Pt C 1 dd) q.1 q.2) (Y.B.A.act Y.w0 i)) = 0
    rw [VP.cc_subst_eq hp00]
    exact (isEndo_act Y Y.w0).cc i)]
  show VP.hAt Y _ _ = VP.hAt Y (EK Y p (kCol Y p col)) (EK Y p (lamAct Y p Y.w0 * kCol Y p col))
  rw [← EK_act]
  congr 1
  · funext i
    exact hbX i
  · funext i
    show MvPowerSeries.subst (fun q : Fin 1 × Fin dd => AA Y p (col, q.2))
        (ev ![pt C dd 0] (Y.B.actK C Y.w0 i)) =
      MvPowerSeries.subst (fun q : Fin 1 × Fin dd => EK Y p (kCol Y p col) q.2) (Y.B.A.act Y.w0 i)
    unfold ev
    rw [MvPowerSeries.subst_comp_subst_apply hp0 hb]
    have hfun : (fun q : Fin 1 × Fin dd => MvPowerSeries.subst (fun q : Fin 1 × Fin dd => AA Y p (col, q.2))
        ((![pt C dd 0] : Fin 1 → Pt C 1 dd) q.1 q.2)) = fun q => EK Y p (kCol Y p col) q.2 := by
      funext q
      rcases q with ⟨j, i⟩
      fin_cases j
      exact hbX i
    rw [hfun]
    congr 1

theorem cc_expPtS (o : Orb) (g : Fin 2) (x : Fin 2 × Fin dd) :
    MvPowerSeries.constantCoeff ((Y.rawSelf (p o)).expPt g x) = 0 := by
  obtain ⟨col, i⟩ := x
  have h0 : MvPowerSeries.constantCoeff (toAllS (I := IS I0) o ((Y.rawSelf (p o)).expPt g (col, i))) = 0 := by
    rw [toAllS_expPtS]
    exact cc_EK Y p _ _
  rw [toAllS, VP.cc_subst_eq] at h0
  · exact h0
  · intro w
    exact MvPowerSeries.constantCoeff_X _

theorem hRow_eqS (o : Orb) : (Y.rawSelf (p o)).hRow = (Y.k : C) • ∑ col : Fin 2,
    VP.hAt Y (fun i => (Y.rawSelf (p o)).expPt 0 (col, i)) (fun i => (Y.rawSelf (p o)).expPt 1 (col, i)) := by
  have hS : MvPowerSeries.HasSubst
      (fun q : Fin 2 × (Fin 2 × Fin dd) => (Y.rawSelf (p o)).expPt q.1 q.2) :=
    by first
      | exact MvPowerSeries.hasSubst_of_constantCoeff_zero fun q => cc_expPtS Y p o q.1 q.2
      | exact MvPowerSeries.HasSubst.of_constantCoeff_nilpotent fun q => by
          rw [cc_expPtS Y p o q.1 q.2]; exact IsNilpotent.zero
  unfold RawChart.hRow
  congr 1
  show MvPowerSeries.subst (fun q : Fin 2 × (Fin 2 × Fin dd) => (Y.rawSelf (p o)).expPt q.1 q.2)
    (∑ col, hCol col Y.h) = _
  rw [← MvPowerSeries.coe_substAlgHom hS, map_sum]
  refine Finset.sum_congr rfl fun col _ => ?_
  have hX : MvPowerSeries.HasSubst (fun q : Fin 2 × Fin dd =>
      (MvPowerSeries.X (q.1, (col, q.2)) : MvPowerSeries (Fin 2 × (Fin 2 × Fin dd)) C)) :=
    by first
      | exact MvPowerSeries.hasSubst_of_constantCoeff_zero fun q => MvPowerSeries.constantCoeff_X _
      | exact MvPowerSeries.HasSubst.of_constantCoeff_nilpotent fun q => by
          rw [MvPowerSeries.constantCoeff_X]; exact IsNilpotent.zero
  rw [MvPowerSeries.coe_substAlgHom, hCol, MvPowerSeries.subst_comp_subst_apply hX hS]
  simp only [MvPowerSeries.subst_X hS]
  unfold VP.hAt
  congr 1
  funext q
  rcases q with ⟨g, i⟩
  fin_cases g <;> first | rfl | simp [VP.P2]

theorem toAllS_hRow (o : Orb) : toAllS (I := IS I0) o (mvExp (Y.rawSelf (p o)).hRow) =
    mvExp ((Y.k : C) • ∑ col, HK Y p (lamG Y p o col 0 * ind (o, 0)) (lamG Y p o col 1 * ind (o, 1))) := by
  have hX : ∀ w : WV (IS I0 o), MvPowerSeries.constantCoeff
      ((MvPowerSeries.X (⟨o, w⟩ : WVO (IS I0))) : MvPowerSeries (WVO (IS I0)) C) = 0 :=
    fun w => MvPowerSeries.constantCoeff_X _
  have hcc : MvPowerSeries.constantCoeff (Y.rawSelf (p o)).hRow = 0 := by
    rw [hRow_eqS, MvPowerSeries.smul_eq_C_mul, map_mul, map_sum,
      Finset.sum_eq_zero fun col _ => VP.cc_hAt (Y := Y) (fun i => cc_expPtS Y p o 0 (col, i))
        (fun i => cc_expPtS Y p o 1 (col, i)), mul_zero]
  have hS : MvPowerSeries.HasSubst (fun w : WV (IS I0 o) =>
      ((MvPowerSeries.X (⟨o, w⟩ : WVO (IS I0))) : MvPowerSeries (WVO (IS I0)) C)) := by
    first
      | exact MvPowerSeries.hasSubst_of_constantCoeff_zero hX
      | exact MvPowerSeries.HasSubst.of_constantCoeff_nilpotent fun w => by
          rw [hX w]; exact IsNilpotent.zero
  unfold toAllS
  rw [VP.subst_exp hX hcc, hRow_eqS]
  congr 1
  rw [← MvPowerSeries.coe_substAlgHom hS, map_smul, map_sum]
  congr 1
  refine Finset.sum_congr rfl fun col _ => ?_
  rw [MvPowerSeries.coe_substAlgHom, VP.hAt_subst (hA := hX) (hu := fun i => cc_expPtS Y p o 0 (col, i))
    (hv := fun i => cc_expPtS Y p o 1 (col, i))]
  show VP.hAt Y _ _ = VP.hAt Y (EK Y p _) (EK Y p _)
  congr 1 <;> funext i <;> exact toAllS_expPtS Y p o _ col i

end VS

theorem unitSelf_of {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {d : ℕ}
    [NeZero d] {Orb : Type} [Fintype Orb] {I0 : Orb → Type} [∀ o, Fintype (I0 o)]
    (Y : FBChart C V O dd) (p : ∀ o, SelfData Y d (I0 o)) (hG : ∀ o, GmPackSt Y (p o)) : UnitSelfSt Y p := by
  intro hs
  choose γ γ' hγ using hG
  have hA := VS.cc_AA Y p
  have hk := VS.Cg.nsmul hA (VS.main_cg hs hγ) Y.k
  obtain ⟨U, hU, hE⟩ := VS.Cg.unit hA hk
  refine ⟨U, hU.1, hU.2, ?_⟩
  have hL : pull2 Y p (∏ col : Fin 2, ev (n := 2) ![pt C dd col] (FB.expS C ((Y.k : C) • Y.B.hL C Y.h Y.w0))) =
      mvExp ((Y.k : C) • ∑ col : Fin 2,
        VS.HK Y p (VS.kCol Y p col) (VS.lamAct Y p Y.w0 * VS.kCol Y p col)) := by
    rw [VP.pullback_two_var_prod]
    simp only [VS.pullback_exp_column]
    rw [Finset.smul_sum, VS.exp_sum]
    intro col _
    exact (VS.Cg.nsmul hA (VS.Cg.refl (V := V) hA (VS.cc_HK Y p _ _)) Y.k).1
  have hR : ∏ o, toAllS (I := IS I0) o (mvExp (Y.rawSelf (p o)).hRow) =
      mvExp ((Y.k : C) • ∑ o, ∑ col, VS.HK Y p (VS.lamG Y p o col 0 * VS.ind (o, 0))
        (VS.lamG Y p o col 1 * VS.ind (o, 1))) := by
    simp only [VS.toAllS_hRow]
    rw [Finset.smul_sum, VS.exp_sum]
    intro o _
    have h0 : MvPowerSeries.constantCoeff (∑ col, VS.HK Y p (VS.lamG Y p o col 0 * VS.ind (o, 0))
        (VS.lamG Y p o col 1 * VS.ind (o, 1))) = 0 := by
      rw [map_sum]
      exact Finset.sum_eq_zero fun _ _ => VS.cc_HK Y p _ _
    exact (VS.Cg.nsmul hA (VS.Cg.refl (V := V) hA h0) Y.k).1
  rw [hL, hR]
  exact hE

end Formalism.L2.FormalSeriesBounds
