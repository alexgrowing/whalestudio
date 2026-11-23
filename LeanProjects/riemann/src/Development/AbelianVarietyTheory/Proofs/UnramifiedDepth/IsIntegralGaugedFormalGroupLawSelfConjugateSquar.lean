import Mathlib
import Formalism.LocalToGlobal.CharacterGerms.NondegenerateCharts
import Formalism.LocalToGlobal.CharacterGerms.RowTieSelf
import Formalism.LocalToGlobal.CharacterGerms.BlockAdmissibleChart
import Formalism.LocalToGlobal.CharacterGerms.NegMem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.CalcExp
import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.HasTeich

set_option autoImplicit false

noncomputable section

open scoped BigOperators
open MvPowerSeries Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace GlobalTheory.RowLawSquare

section Series

variable {C : Type} [Field C] {σ τ : Type}

def intSer (V : VF C) (σ : Type) : Subring (MvPowerSeries σ C) where
  carrier := {f | IntS V f}
  mul_mem' := by
    classical
    intro f g hf hg μ
    rw [coeff_mul]
    exact VF.Ge.sum fun p _ => (hf _).mul_int (hg _)
  one_mem' := by
    classical
    intro μ
    rw [coeff_one]
    split_ifs
    · exact VF.Ge.one
    · exact VF.Ge.zero 0
  add_mem' := fun hf hg μ => by rw [map_add]; exact (hf μ).add (hg μ)
  zero_mem' := fun μ => by rw [map_zero]; exact VF.Ge.zero 0
  neg_mem' := fun hf μ => by rw [map_neg]; exact (hf μ).neg

theorem intS_X (V : VF C) (s : σ) : IntS V (X s : MvPowerSeries σ C) := by
  classical
  intro μ
  rw [coeff_X]
  split_ifs
  · exact VF.Ge.one
  · exact VF.Ge.zero 0

theorem intS_subst (V : VF C) [Finite σ] {a : σ → MvPowerSeries τ C} (h0 : ∀ s, constantCoeff (a s) = 0)
    (ha : ∀ s, IntS V (a s)) {f : MvPowerSeries σ C} (hf : IntS V f) : IntS V (subst a f) := by
  intro μ
  rw [coeff_subst (hasSubst_of_constantCoeff_zero h0)]
  refine finsum_induction (V.Ge 0) (VF.Ge.zero 0) (fun _ _ hx hy => hx.add hy) fun e => ?_
  have : (e.prod fun s m => a s ^ m) ∈ intSer V τ :=
    Subring.prod_mem _ fun s _ => Subring.pow_mem _ (ha s) _
  exact (hf e).mul_int (this μ)

theorem mvExp_eq [CharZero C] {h : MvPowerSeries σ C} (h0 : constantCoeff h = 0) :
    mvExp h = PowerSeries.subst h (PowerSeries.exp C) := by
  ext m
  rw [PowerSeries.coeff_subst (PowerSeries.HasSubst.of_constantCoeff_zero h0),
    finsum_eq_sum_of_support_subset (s := Finset.range (m.degree + 1))]
  · show ∑ k ∈ Finset.range (m.degree + 1), coeff m (h ^ k) / (k.factorial : C) = _
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [PowerSeries.coeff_exp, smul_eq_mul]
    simp [div_eq_inv_mul]
  · intro k hk
    rw [Function.mem_support] at hk
    by_contra hc
    apply hk
    rw [coeff_of_lt_order, smul_zero]
    refine lt_of_lt_of_le ?_ (le_order_pow_of_constantCoeff_eq_zero k h0)
    simp only [Finset.coe_range, Set.mem_Iio, not_lt] at hc
    exact_mod_cast hc

theorem coeff_rename_low [Finite σ] (φ : σ → τ) {f g : MvPowerSeries σ C} {N : ℕ}
    (hfg : ∀ e : σ →₀ ℕ, e.degree ≤ N → coeff e f = coeff e g) (μ : τ →₀ ℕ) (hμ : μ.degree ≤ N) :
    coeff μ (subst (fun s => (X (φ s) : MvPowerSeries τ C)) f) =
      coeff μ (subst (fun s => (X (φ s) : MvPowerSeries τ C)) g) := by
  have hS : HasSubst (fun s => (X (φ s) : MvPowerSeries τ C)) :=
    hasSubst_of_constantCoeff_zero fun s => constantCoeff_X _
  rw [coeff_subst hS, coeff_subst hS]
  refine finsum_congr fun e => ?_
  by_cases he : e.degree ≤ N
  · rw [hfg e he]
  · have h1 : (e.prod fun s m => (X (φ s) : MvPowerSeries τ C) ^ m) = monomial (e.mapDomain φ) 1 := by
      rw [monomial_one_eq, Finsupp.prod_mapDomain_index (by simp) (fun _ _ _ => pow_add _ _ _)]
    have h2 : μ ≠ e.mapDomain φ := by
      rintro rfl
      apply he
      rwa [Finsupp.degree_mapDomain] at hμ
    rw [h1, coeff_monomial_ne h2, smul_zero, smul_zero]

variable {dd : ℕ}

theorem subst_singlePointUncurry {a : Fin dd → MvPowerSeries τ C} (ha : ∀ i, constantCoeff (a i) = 0) (f : PS C 1 dd) :
    subst a (un1 f) = subst (fun p : Fin 1 × Fin dd => a p.2) f := by
  ext μ
  let e : Fin dd ≃ Fin 1 × Fin dd :=
    ⟨fun x => (0, x), fun p => p.2, fun _ => rfl, fun p => Prod.ext (Subsingleton.elim _ _) rfl⟩
  rw [coeff_subst (hasSubst_of_constantCoeff_zero ha),
    coeff_subst (hasSubst_of_constantCoeff_zero fun p : Fin 1 × Fin dd => ha p.2),
    ← finsum_comp_equiv (Finsupp.domCongr (M := ℕ) e).toEquiv]
  refine finsum_congr fun ν => ?_
  have h1 : (Finsupp.domCongr (M := ℕ) e).toEquiv ν = ν.mapDomain fun x : Fin dd => ((0 : Fin 1), x) :=
    Finsupp.equivMapDomain_eq_mapDomain e ν
  rw [h1, Finsupp.prod_mapDomain_index (by simp) (fun _ _ _ => pow_add _ _ _)]
  rfl

def sb {n : ℕ} (a : Fin n → Fin dd → MvPowerSeries τ C) (f : PS C n dd) : MvPowerSeries τ C :=
  subst (fun p : Fin n × Fin dd => a p.1 p.2) f

def Zc {ι : Type} (a : ι → MvPowerSeries τ C) : Prop := ∀ i, constantCoeff (a i) = 0

theorem hasSubst_sb {n : ℕ} {a : Fin n → Fin dd → MvPowerSeries τ C} (ha : ∀ j, Zc (a j)) :
    HasSubst (fun p : Fin n × Fin dd => a p.1 p.2) :=
  hasSubst_of_constantCoeff_zero fun p => ha p.1 p.2

theorem sb_ev {m n : ℕ} {a : Fin n → Fin dd → MvPowerSeries τ C} (ha : ∀ j, Zc (a j))
    {b : Fin m → Pt C n dd} (hb : ∀ j, Zc (b j)) (f : PS C m dd) :
    sb a (ev b f) = sb (fun j i => sb a (b j i)) f :=
  subst_comp_subst_apply (hasSubst_sb hb) (hasSubst_sb ha) f

theorem sb_pt {n : ℕ} {a : Fin n → Fin dd → MvPowerSeries τ C} (ha : ∀ j, Zc (a j)) (j : Fin n) (i : Fin dd) :
    sb a (pt C dd j i) = a j i :=
  subst_X (hasSubst_sb ha) (j, i)

theorem zc_pt {n : ℕ} (j : Fin n) : Zc (pt C dd j) := fun _ => constantCoeff_X _

theorem cc_sb {n : ℕ} {a : Fin n → Fin dd → MvPowerSeries τ C} (ha : ∀ j, Zc (a j)) {f : PS C n dd}
    (hf : constantCoeff f = 0) : constantCoeff (sb a f) = 0 :=
  constantCoeff_subst_eq_zero (hasSubst_sb ha) (fun p => ha p.1 p.2) hf

theorem zc1 {a : Fin dd → MvPowerSeries τ C} (ha : Zc a) : ∀ j, Zc (![a] j) := by
  intro j; fin_cases j; exact ha

theorem zc2 {a b : Fin dd → MvPowerSeries τ C} (ha : Zc a) (hb : Zc b) : ∀ j, Zc (![a, b] j) := by
  intro j; fin_cases j; exacts [ha, hb]

theorem zc3 {a b c : Fin dd → MvPowerSeries τ C} (ha : Zc a) (hb : Zc b) (hc : Zc c) :
    ∀ j, Zc (![a, b, c] j) := by
  intro j; fin_cases j; exacts [ha, hb, hc]

theorem substPointsPowerSeries_eval_one {n : ℕ} {a : Fin n → Fin dd → MvPowerSeries τ C} (ha : ∀ j, Zc (a j))
    {b : Pt C n dd} (hb : Zc b) (f : PS C 1 dd) :
    sb a (ev ![b] f) = sb ![fun i => sb a (b i)] f := by
  rw [sb_ev ha (zc1 hb)]
  congr 1
  funext j
  fin_cases j
  rfl

theorem substPointsPowerSeries_eval_two {n : ℕ} {a : Fin n → Fin dd → MvPowerSeries τ C} (ha : ∀ j, Zc (a j))
    {b c : Pt C n dd} (hb : Zc b) (hc : Zc c) (f : PS C 2 dd) :
    sb a (ev ![b, c] f) = sb ![fun i => sb a (b i), fun i => sb a (c i)] f := by
  rw [sb_ev ha (zc2 hb hc)]
  refine congrArg (fun A => sb A f) ?_
  funext j
  fin_cases j
  · simp
  · simp

theorem sb_pt' {n : ℕ} {a : Fin n → Fin dd → MvPowerSeries τ C} (ha : ∀ j, Zc (a j)) (j : Fin n) :
    (fun i => sb a (pt C dd j i)) = a j := funext (sb_pt ha j)

theorem intS_sb (V : VF C) {n : ℕ} {a : Fin n → Fin dd → MvPowerSeries τ C} (ha : ∀ j, Zc (a j))
    (hi : ∀ j i, IntS V (a j i)) {f : PS C n dd} (hf : IntS V f) : IntS V (sb a f) :=
  intS_subst V (a := fun p : Fin n × Fin dd => a p.1 p.2) (fun p => ha p.1 p.2) (fun p => hi p.1 p.2) hf

theorem sb_add {n : ℕ} {a : Fin n → Fin dd → MvPowerSeries τ C} (ha : ∀ j, Zc (a j)) (f g : PS C n dd) :
    sb a (f + g) = sb a f + sb a g := subst_add (hasSubst_sb ha) f g

theorem sb_sub {n : ℕ} {a : Fin n → Fin dd → MvPowerSeries τ C} (ha : ∀ j, Zc (a j)) (f g : PS C n dd) :
    sb a (f - g) = sb a f - sb a g := subst_sub (hasSubst_sb ha) f g

theorem subst_inCol {a : Fin 2 × Fin dd → MvPowerSeries τ C} (ha : Zc a) (col : Fin 2) (f : PS C 1 dd) :
    subst a (inCol col (un1 f)) = sb ![fun x => a (col, x)] f := by
  have hA := hasSubst_of_constantCoeff_zero ha
  unfold inCol
  rw [subst_comp_subst_apply (hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _) hA]
  simp only [subst_X hA]
  rw [subst_singlePointUncurry (fun i => ha _)]
  unfold sb
  congr 1
  funext p
  obtain ⟨j, i⟩ := p
  fin_cases j
  rfl

theorem subst_hCol {a : Fin 2 × (Fin 2 × Fin dd) → MvPowerSeries τ C} (ha : Zc a) (col : Fin 2) (f : PS C 2 dd) :
    subst a (hCol col f) = sb ![fun x => a (0, (col, x)), fun x => a (1, (col, x))] f := by
  have hA := hasSubst_of_constantCoeff_zero ha
  unfold hCol
  rw [subst_comp_subst_apply (hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _) hA]
  simp only [subst_X hA]
  unfold sb
  congr 1
  funext p
  obtain ⟨j, i⟩ := p
  fin_cases j <;> rfl

theorem map_self (f : MvPowerSeries σ C) : MvPowerSeries.map (algebraMap C C) f = f := by
  ext n
  simp [coeff_map]

end Series

section Chart

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}
  (Y : FBChart C V O dd) {τ : Type}

theorem zc_lg : Zc Y.lg := fun i => by
  rw [← coeff_zero_eq_constantCoeff_apply, Y.lg_lin i 0 (by simp), coeff_zero_eq_constantCoeff_apply,
    constantCoeff_X]

theorem h_axes (g : Fin 2) : ∀ e : Fin 2 × Fin dd →₀ ℕ, (∀ s ∈ e.support, s.1 ≠ g) → coeff e Y.h = 0 := by
  fin_cases g
  · refine coeff_of_ev_zero Y.h 0 ![0, pt C dd 0] rfl ?_ Y.gauge.ax0
    intro g' hg'
    rw [fin_two_eq_one_sub_of_ne' 0 g' hg']
    rfl
  · refine coeff_of_ev_zero Y.h 1 ![pt C dd 0, 0] rfl ?_ Y.gauge.ax1
    intro g' hg'
    rw [fin_two_eq_one_sub_of_ne' 1 g' hg']
    rfl

theorem cc_h : constantCoeff Y.h = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply]
  exact h_axes Y 0 0 (by simp)

theorem FK_self : Y.B.FK C = Y.B.G.F := funext fun _ => map_self _

def law (a b : Fin dd → MvPowerSeries τ C) : Fin dd → MvPowerSeries τ C := fun i => sb ![a, b] (Y.B.G.F i)

theorem zc_law {a b : Fin dd → MvPowerSeries τ C} (ha : Zc a) (hb : Zc b) : Zc (law Y a b) :=
  fun i => cc_sb (zc2 ha hb) (Y.B.G.const i)

theorem zc_addOf {n : ℕ} (j k : Fin n) : Zc (addOf Y.B.G.F (pt C dd j) (pt C dd k)) :=
  zc_law Y (zc_pt j) (zc_pt k)

theorem sb_addOf {n : ℕ} {a : Fin n → Fin dd → MvPowerSeries τ C} (ha : ∀ j, Zc (a j)) (j k : Fin n) :
    (fun i => sb a (addOf Y.B.G.F (pt C dd j) (pt C dd k) i)) = law Y (a j) (a k) := by
  funext i
  rw [addOf, substPointsPowerSeries_eval_two ha (zc_pt j) (zc_pt k), sb_pt' ha, sb_pt' ha]
  rfl

theorem lg_law {a b : Fin dd → MvPowerSeries τ C} (ha : Zc a) (hb : Zc b) (i : Fin dd) :
    sb ![a] (Y.lg i) + sb ![b] (Y.lg i) = sb ![law Y a b] (Y.lg i) := by
  have h2 := zc2 ha hb
  have e := congrArg (sb ![a, b]) (Y.lg_add i)
  rw [substPointsPowerSeries_eval_one h2 (zc_addOf Y 0 1), sb_addOf Y h2, sb_add h2, substPointsPowerSeries_eval_one h2 (zc_pt 0), substPointsPowerSeries_eval_one h2 (zc_pt 1), sb_pt' h2, sb_pt' h2] at e
  exact e.symm

theorem ex_lg {a : Fin dd → MvPowerSeries τ C} (ha : Zc a) (i : Fin dd) :
    sb ![fun x => sb ![a] (Y.lg x)] (Y.ex i) = a i := by
  have e := congrArg (sb ![a]) (congrFun Y.ex_lg i)
  rw [comp1, substPointsPowerSeries_eval_one (zc1 ha) (zc_lg Y), sb_pt (zc1 ha)] at e
  exact e

theorem lg_ex {a : Fin dd → MvPowerSeries τ C} (ha : Zc a) (i : Fin dd) :
    sb ![fun x => sb ![a] (Y.ex x)] (Y.lg i) = a i := by
  have e := congrArg (sb ![a]) (congrFun Y.lg_ex i)
  rw [comp1, substPointsPowerSeries_eval_one (zc1 ha) Y.ex_const, sb_pt (zc1 ha)] at e
  exact e

theorem sb_exp {n : ℕ} {a : Fin n → Fin dd → MvPowerSeries τ C} (ha : ∀ j, Zc (a j)) {f : PS C n dd}
    (hf : constantCoeff f = 0) : sb a (FB.expS C f) = PowerSeries.subst (sb a f) (PowerSeries.exp C) :=
  ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.subst_exp (fun p : Fin n × Fin dd => a p.1 p.2) (fun p => ha p.1 p.2) hf

theorem cc_hev {n : ℕ} {b c : Pt C n dd} (hb : Zc b) (hc : Zc c) : constantCoeff (ev ![b, c] Y.h) = 0 :=
  cc_sb (zc2 hb hc) (cc_h Y)

theorem exp_gauge_cocycle_first_variable {a b c : Fin dd → MvPowerSeries τ C} (ha : Zc a) (hb : Zc b) (hc : Zc c) :
    PowerSeries.subst (sb ![a, c] Y.h + sb ![b, c] Y.h - sb ![law Y a b, c] Y.h) (PowerSeries.exp C) =
      sb ![a, b, c] Y.B.ph1 := by
  have h3 := zc3 ha hb hc
  have e := Y.gauge.ph1
  rw [FB.toK, map_self, FK_self] at e
  rw [e, sb_exp h3 (by
      rw [map_sub, map_add, cc_hev Y (zc_pt _) (zc_pt _), cc_hev Y (zc_pt _) (zc_pt _),
        cc_hev Y (zc_addOf Y _ _) (zc_pt _)]
      simp),
    sb_sub h3, sb_add h3, substPointsPowerSeries_eval_two h3 (zc_pt _) (zc_pt _), substPointsPowerSeries_eval_two h3 (zc_pt _) (zc_pt _),
    substPointsPowerSeries_eval_two h3 (zc_addOf Y _ _) (zc_pt _), sb_addOf Y h3, sb_pt' h3, sb_pt' h3, sb_pt' h3]
  rfl

theorem exp_gauge_cocycle_second_variable {a b c : Fin dd → MvPowerSeries τ C} (ha : Zc a) (hb : Zc b) (hc : Zc c) :
    PowerSeries.subst (sb ![a, b] Y.h + sb ![a, c] Y.h - sb ![a, law Y b c] Y.h) (PowerSeries.exp C) =
      sb ![a, b, c] Y.B.ph2 := by
  have h3 := zc3 ha hb hc
  have e := Y.gauge.ph2
  rw [FB.toK, map_self, FK_self] at e
  rw [e, sb_exp h3 (by
      rw [map_sub, map_add, cc_hev Y (zc_pt _) (zc_pt _), cc_hev Y (zc_pt _) (zc_pt _),
        cc_hev Y (zc_pt _) (zc_addOf Y _ _)]
      simp),
    sb_sub h3, sb_add h3, substPointsPowerSeries_eval_two h3 (zc_pt _) (zc_pt _), substPointsPowerSeries_eval_two h3 (zc_pt _) (zc_pt _),
    substPointsPowerSeries_eval_two h3 (zc_pt _) (zc_addOf Y _ _), sb_addOf Y h3, sb_pt' h3, sb_pt' h3, sb_pt' h3]
  rfl

theorem exp_sy {a b : Fin dd → MvPowerSeries τ C} (ha : Zc a) (hb : Zc b) :
    PowerSeries.subst (sb ![b, a] Y.h - sb ![a, b] Y.h) (PowerSeries.exp C) = sb ![a, b] Y.B.sy := by
  have h2 := zc2 ha hb
  have e := Y.gauge.sy
  rw [FB.toK, map_self] at e
  rw [e, sb_exp h2 (by
      rw [map_sub, cc_hev Y (zc_pt _) (zc_pt _), cc_h]
      simp),
    sb_sub h2, substPointsPowerSeries_eval_two h2 (zc_pt _) (zc_pt _), sb_pt' h2, sb_pt' h2]
  rfl

variable {d : ℕ} {I0 : Type} [Fintype I0] (p : SelfData Y d I0)

def colOf (a : Fin 2 × Fin dd → MvPowerSeries τ C) (col : Fin 2) : Fin dd → MvPowerSeries τ C := fun x => a (col, x)

omit [CharZero C] in
theorem zc_col {a : Fin 2 × Fin dd → MvPowerSeries τ C} (ha : Zc a) (col : Fin 2) : Zc (colOf a col) :=
  fun _ => ha _

theorem subst_lg {a : Fin 2 × Fin dd → MvPowerSeries τ C} (ha : Zc a) (x : Fin 2 × Fin dd) :
    subst a ((Y.rawSelf p).lg x) = sb ![colOf a x.1] (Y.lg x.2) := subst_inCol ha _ _

theorem subst_ex {a : Fin 2 × Fin dd → MvPowerSeries τ C} (ha : Zc a) (x : Fin 2 × Fin dd) :
    subst a ((Y.rawSelf p).ex x) = sb ![colOf a x.1] (Y.ex x.2) := subst_inCol ha _ _

theorem formalAdd_eq {a b : Fin 2 × Fin dd → MvPowerSeries τ C} (ha : Zc a) (hb : Zc b) (x : Fin 2 × Fin dd) :
    addP (Y.rawSelf p) a b x = law Y (colOf a x.1) (colOf b x.1) x.2 := by
  unfold addP
  simp only [subst_lg Y p ha, subst_lg Y p hb, lg_law Y (zc_col ha _) (zc_col hb _)]
  rw [subst_ex Y p fun y => cc_sb (zc1 (zc_law Y (zc_col ha _) (zc_col hb _))) (zc_lg Y _)]
  exact ex_lg Y (zc_law Y (zc_col ha _) (zc_col hb _)) _

theorem zc_addP {a b : Fin 2 × Fin dd → MvPowerSeries τ C} (ha : Zc a) (hb : Zc b) :
    Zc (addP (Y.rawSelf p) a b) := fun x => by
  rw [formalAdd_eq Y p ha hb]
  exact zc_law Y (zc_col ha _) (zc_col hb _) _

theorem col_addP {a b : Fin 2 × Fin dd → MvPowerSeries τ C} (ha : Zc a) (hb : Zc b) (col : Fin 2) :
    colOf (addP (Y.rawSelf p) a b) col = law Y (colOf a col) (colOf b col) :=
  funext fun x => formalAdd_eq Y p ha hb (col, x)

theorem hAt_eq {a b : Fin 2 × Fin dd → MvPowerSeries τ C} (ha : Zc a) (hb : Zc b) :
    hAt (Y.rawSelf p) a b = sb ![colOf a 0, colOf b 0] Y.h + sb ![colOf a 1, colOf b 1] Y.h := by
  have hz : Zc (fun q : Fin 2 × (Fin 2 × Fin dd) => if q.1 = 0 then a q.2 else b q.2) := fun q => by
    dsimp only
    split_ifs
    exacts [ha _, hb _]
  unfold hAt
  show subst _ (∑ col, hCol col Y.h) = _
  rw [Fin.sum_univ_two, subst_add (hasSubst_of_constantCoeff_zero hz), subst_hCol hz, subst_hCol hz]
  simp only [if_true, one_ne_zero, if_false]
  rfl

omit [CharZero C] in
theorem zc_gp {κ : Type} {n : ℕ} (j : Fin n) : Zc (gp C κ j) := fun _ => constantCoeff_X _

theorem h_eq : (Y.rawSelf p).h = hAt (Y.rawSelf p) (gp C _ (0 : Fin 2)) (gp C _ 1) := by
  unfold hAt
  have : (fun q : Fin 2 × (Fin 2 × Fin dd) => if q.1 = 0 then gp C (Fin 2 × Fin dd) (0 : Fin 2) q.2
      else gp C (Fin 2 × Fin dd) 1 q.2) = X := by
    funext ⟨j, x⟩
    fin_cases j <;> simp [gp]
  rw [this, subst_self]
  rfl

theorem intS_exp_add {f g : MvPowerSeries τ C} (hf : constantCoeff f = 0) (hg : constantCoeff g = 0)
    (hf' : IntS V (PowerSeries.subst f (PowerSeries.exp C)))
    (hg' : IntS V (PowerSeries.subst g (PowerSeries.exp C))) : IntS V (mvExp (f + g)) := by
  rw [mvExp_eq (by simp [hf, hg]), ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.exp_add hf hg]
  exact (intSer V τ).mul_mem hf' hg'

theorem cc_hsb {a b : Fin dd → MvPowerSeries τ C} (ha : Zc a) (hb : Zc b) : constantCoeff (sb ![a, b] Y.h) = 0 :=
  cc_sb (zc2 ha hb) (cc_h Y)

theorem gm_int (a : ZMod d) (r s : Fin 2) : V.Ge 0 (p.gm a r s) := by
  obtain ⟨M, hM⟩ := p.gm_lim 0
  have h := hM a r s
  rw [Nat.cast_zero] at h
  simpa using h.add (p.em_int a (M r s))

end Chart

theorem rlaw_rawSelf (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] [StarRing O] (dd : ℕ)
    (Y : FBChart C V O dd) (d : ℕ) [NeZero d] (I0 : Type) [Fintype I0] (p : SelfData Y d I0) :
    RLaw (Y.rawSelf p) V where
  charZero := inferInstance
  closed := Y.algClosed
  odd := Y.l_odd
  lin := by
    intro x μ hμ
    have hX : Zc (X : Fin 2 × Fin dd → MvPowerSeries (Fin 2 × Fin dd) C) := fun _ => constantCoeff_X _
    have e := subst_lg Y p hX x
    rw [subst_self, id] at e
    have e2 : (fun q : Fin 1 × Fin dd => (![colOf (X : Fin 2 × Fin dd → MvPowerSeries (Fin 2 × Fin dd) C) x.1] :
        Fin 1 → Fin dd → MvPowerSeries (Fin 2 × Fin dd) C) q.1 q.2) = fun q => X (x.1, q.2) := by
      funext ⟨j, i⟩
      fin_cases j
      rfl
    rw [e, sb, e2, coeff_rename_low (fun q : Fin 1 × Fin dd => (x.1, q.2)) (Y.lg_lin x.2) μ hμ,
      subst_X (hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _)]
  exc := by
    intro x
    have hX : Zc (X : Fin 2 × Fin dd → MvPowerSeries (Fin 2 × Fin dd) C) := fun _ => constantCoeff_X _
    have e := subst_ex Y p hX x
    rw [subst_self, id] at e
    rw [e]
    exact cc_sb (zc1 (zc_col hX _)) (Y.ex_const _)
  lgex := by
    intro x
    have hX : Zc (X : Fin 2 × Fin dd → MvPowerSeries (Fin 2 × Fin dd) C) := fun _ => constantCoeff_X _
    have e : (Y.rawSelf p).ex = fun y => sb ![colOf X y.1] (Y.ex y.2) := by
      funext y
      rw [← subst_ex Y p hX y, subst_self, id]
    rw [e, subst_lg Y p fun y => cc_sb (zc1 (zc_col hX _)) (Y.ex_const _)]
    exact lg_ex Y (zc_col hX x.1) x.2
  exlg := by
    intro x
    have hX : Zc (X : Fin 2 × Fin dd → MvPowerSeries (Fin 2 × Fin dd) C) := fun _ => constantCoeff_X _
    have e : (Y.rawSelf p).lg = fun y => sb ![colOf X y.1] (Y.lg y.2) := by
      funext y
      rw [← subst_lg Y p hX y, subst_self, id]
    rw [e, subst_ex Y p fun y => cc_sb (zc1 (zc_col hX _)) (zc_lg Y _)]
    exact ex_lg Y (zc_col hX x.1) x.2
  axes := by
    classical
    intro g e he
    show coeff e (∑ col, hCol col Y.h) = 0
    rw [map_sum]
    refine Finset.sum_eq_zero fun col _ => ?_
    refine Van.subst (T := {s : Fin 2 × (Fin 2 × Fin dd) | s.1 = g}) {s : Fin 2 × Fin dd | s.1 = g}
      (fun _ => constantCoeff_X _) ?_ (h_axes Y g) e he
    intro s hs ν hν
    rw [coeff_X, if_neg]
    rintro rfl
    exact hν (s.1, (col, s.2)) (by simp) hs
  addInt := by
    intro x
    rw [formalAdd_eq Y p (zc_gp _) (zc_gp _)]
    refine intS_sb V (zc2 (zc_col (zc_gp _) _) (zc_col (zc_gp _) _)) ?_ (Y.intF _)
    intro j i
    fin_cases j <;> exact intS_X V _
  ph1 := by
    have z := fun (j : Fin 3) (col : Fin 2) => zc_col (zc_gp (C := C) (κ := Fin 2 × Fin dd) j) col
    rw [hAt_eq Y p (zc_gp _) (zc_gp _), hAt_eq Y p (zc_gp _) (zc_gp _),
      hAt_eq Y p (zc_addP Y p (zc_gp _) (zc_gp _)) (zc_gp _), col_addP Y p (zc_gp _) (zc_gp _),
      col_addP Y p (zc_gp _) (zc_gp _), add_add_add_comm, add_sub_add_comm]
    refine intS_exp_add ?_ ?_ ?_ ?_
    iterate 2
      rw [map_sub, map_add, cc_hsb Y (z _ _) (z _ _), cc_hsb Y (z _ _) (z _ _),
        cc_hsb Y (zc_law Y (z _ _) (z _ _)) (z _ _), add_zero, sub_zero]
    all_goals
      rw [exp_gauge_cocycle_first_variable Y (z _ _) (z _ _) (z _ _)]
      refine intS_sb V (zc3 (z _ _) (z _ _) (z _ _)) ?_ Y.intPh1
      intro j i
      fin_cases j <;> exact intS_X V _
  ph2 := by
    have z := fun (j : Fin 3) (col : Fin 2) => zc_col (zc_gp (C := C) (κ := Fin 2 × Fin dd) j) col
    rw [hAt_eq Y p (zc_gp _) (zc_gp _), hAt_eq Y p (zc_gp _) (zc_gp _),
      hAt_eq Y p (zc_gp _) (zc_addP Y p (zc_gp _) (zc_gp _)), col_addP Y p (zc_gp _) (zc_gp _),
      col_addP Y p (zc_gp _) (zc_gp _), add_add_add_comm, add_sub_add_comm]
    refine intS_exp_add ?_ ?_ ?_ ?_
    iterate 2
      rw [map_sub, map_add, cc_hsb Y (z _ _) (z _ _), cc_hsb Y (z _ _) (z _ _),
        cc_hsb Y (z _ _) (zc_law Y (z _ _) (z _ _)), add_zero, sub_zero]
    all_goals
      rw [exp_gauge_cocycle_second_variable Y (z _ _) (z _ _) (z _ _)]
      refine intS_sb V (zc3 (z _ _) (z _ _) (z _ _)) ?_ Y.intPh2
      intro j i
      fin_cases j <;> exact intS_X V _
  sy := by
    have z := fun (j : Fin 2) (col : Fin 2) => zc_col (zc_gp (C := C) (κ := Fin 2 × Fin dd) j) col
    rw [h_eq Y p, hAt_eq Y p (zc_gp _) (zc_gp _), hAt_eq Y p (zc_gp _) (zc_gp _), add_sub_add_comm]
    refine intS_exp_add ?_ ?_ ?_ ?_
    iterate 2
      rw [map_sub, cc_hsb Y (z _ _) (z _ _), cc_hsb Y (z _ _) (z _ _), sub_zero]
    all_goals
      rw [exp_sy Y (z _ _) (z _ _)]
      refine intS_sb V (zc2 (z _ _) (z _ _)) ?_ Y.intSy
      intro j i
      fin_cases j <;> exact intS_X V _
  kunit := Y.k_unit
  uint := fun g c x => (gm_int Y p _ _ _).mul_int (p.e_int c x.2)
  sat := by
    intro g
    obtain ⟨w, hw, hew⟩ := p.e_sat
    refine ⟨fun x c => p.gm (p.ty0 c + p.hd) x.1 (1 - g) * w x.2 c,
      fun x c => (gm_int Y p _ _ _).mul_int (hw _ _), fun c c' => ?_⟩
    have key : ∑ x : Fin 2 × Fin dd, (Y.rawSelf p).u g c x * (p.gm (p.ty0 c' + p.hd) x.1 (1 - g) * w x.2 c') =
        (∑ r, p.gm (p.ty0 c' + p.hd) r (1 - g) * p.gm (p.ty0 c) r g) * ∑ x, p.e c x * w x c' := by
      rw [Finset.sum_mul_sum, Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun x _ => ?_
      show p.gm (p.ty0 c) r g * p.e c x * _ = _
      ring
    refine ⟨fun h => ?_, fun h => ?_⟩
    · subst h
      have hg : 1 - g ≠ g := by fin_cases g <;> decide
      rw [key, hew, p.gm_hyp, if_neg hg, if_pos rfl, one_mul]
    · rw [key, hew, if_neg h, mul_zero]

end GlobalTheory.RowLawSquare
