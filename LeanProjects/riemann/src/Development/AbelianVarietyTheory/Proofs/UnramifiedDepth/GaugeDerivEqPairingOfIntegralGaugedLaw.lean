import Mathlib
import Formalism.LocalToGlobal.CharacterGerms.NondegenerateCharts
import Formalism.LocalToGlobal.CharacterGerms.RowTieSelf
import Formalism.LocalToGlobal.CharacterGerms.BlockAdmissibleChart
import Formalism.LocalToGlobal.CharacterGerms.NegMem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.LogChain
import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.HasTeich

noncomputable section

open scoped BigOperators
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds MvPowerSeries

namespace GlobalTheory.RowLaw.GaugeDeriv

variable {C : Type} [Field C] {V : VF C} {σ τ υ : Type}

theorem int_zero : IntS V (0 : MvPowerSeries σ C) := fun μ => by rw [map_zero]; exact VF.Ge.zero 0

theorem int_add {f g : MvPowerSeries σ C} (hf : IntS V f) (hg : IntS V g) : IntS V (f + g) :=
  fun μ => by rw [map_add]; exact (hf μ).add (hg μ)

theorem int_sub {f g : MvPowerSeries σ C} (hf : IntS V f) (hg : IntS V g) : IntS V (f - g) :=
  fun μ => by rw [map_sub]; exact (hf μ).sub (hg μ)

theorem int_neg {f : MvPowerSeries σ C} (hf : IntS V f) : IntS V (-f) :=
  fun μ => by rw [map_neg]; exact (hf μ).neg

theorem int_smul {c : C} (hc : V.Ge 0 c) {f : MvPowerSeries σ C} (hf : IntS V f) : IntS V (c • f) :=
  fun μ => by rw [coeff_smul]; exact hc.mul_int (hf μ)

theorem int_mul {f g : MvPowerSeries σ C} (hf : IntS V f) (hg : IntS V g) : IntS V (f * g) := by
  classical
  intro μ
  rw [coeff_mul]
  exact VF.Ge.sum fun p _ => (hf _).mul_int (hg _)

theorem int_C {c : C} (hc : V.Ge 0 c) : IntS V (MvPowerSeries.C c : MvPowerSeries σ C) := by
  classical
  intro μ
  rw [coeff_C]
  split_ifs
  · exact hc
  · exact VF.Ge.zero 0

theorem int_one : IntS V (1 : MvPowerSeries σ C) := by
  simpa using (int_C (σ := σ) (VF.Ge.one (V := V)))

theorem int_X (s : σ) : IntS V (X s : MvPowerSeries σ C) := by
  classical
  intro μ
  rw [coeff_X]
  split_ifs
  · exact VF.Ge.one
  · exact VF.Ge.zero 0

theorem int_sum {ι : Type} {s : Finset ι} {f : ι → MvPowerSeries σ C} (h : ∀ i ∈ s, IntS V (f i)) :
    IntS V (∑ i ∈ s, f i) :=
  fun μ => by rw [map_sum]; exact VF.Ge.sum fun i hi => h i hi μ

theorem int_pow {f : MvPowerSeries σ C} (hf : IntS V f) (n : ℕ) : IntS V (f ^ n) := by
  induction n with
  | zero => simpa using int_one
  | succ n ih => rw [pow_succ]; exact int_mul ih hf

theorem int_prod {ι : Type} {s : Finset ι} {f : ι → MvPowerSeries σ C} (h : ∀ i ∈ s, IntS V (f i)) :
    IntS V (∏ i ∈ s, f i) :=
  Finset.prod_induction f (IntS V) (fun _ _ => int_mul) int_one h

theorem int_subst [Finite σ] {a : σ → MvPowerSeries τ C} (ha : ∀ s, constantCoeff (a s) = 0)
    (hi : ∀ s, IntS V (a s)) {f : MvPowerSeries σ C} (hf : IntS V f) : IntS V (subst a f) := by
  intro μ
  rw [coeff_subst (hasSubst_of_constantCoeff_zero ha)]
  refine finsum_induction (V.Ge 0) (VF.Ge.zero 0) (fun _ _ => VF.Ge.add) fun e => ?_
  rw [smul_eq_mul]
  exact (hf e).mul_int (int_prod (fun s _ => int_pow (hi s) _) μ)

theorem int_pderiv {f : MvPowerSeries σ C} (hf : IntS V f) (s : σ) : IntS V (pderiv C s f) := by
  intro μ
  rw [coeff_pderiv, mul_comm]
  refine VF.Ge.mul_int ?_ (hf _)
  exact_mod_cast VF.ge_natCast (V := V) (μ s + 1)

theorem subst_subst [Finite σ] [Finite τ] {a : σ → MvPowerSeries τ C} (ha : ∀ s, constantCoeff (a s) = 0)
    {b : τ → MvPowerSeries υ C} (hb : ∀ s, constantCoeff (b s) = 0) (f : MvPowerSeries σ C) :
    subst b (subst a f) = subst (fun s => subst b (a s)) f :=
  subst_comp_subst_apply (hasSubst_of_constantCoeff_zero ha) (hasSubst_of_constantCoeff_zero hb) f

theorem subst_sum' [Finite σ] {a : σ → MvPowerSeries τ C} (ha : ∀ s, constantCoeff (a s) = 0) {ι : Type}
    (s : Finset ι) (f : ι → MvPowerSeries σ C) : subst a (∑ i ∈ s, f i) = ∑ i ∈ s, subst a (f i) := by
  rw [← coe_substAlgHom (hasSubst_of_constantCoeff_zero ha), map_sum]

theorem subst_zero' [Finite σ] {a : σ → MvPowerSeries τ C} (ha : ∀ s, constantCoeff (a s) = 0) :
    subst a (0 : MvPowerSeries σ C) = 0 := by
  rw [← coe_substAlgHom (hasSubst_of_constantCoeff_zero ha), map_zero]

theorem coeff_psubst {a : MvPowerSeries τ C} (ha : constantCoeff a = 0) (f : PowerSeries C) (μ : τ →₀ ℕ) :
    coeff μ (subst (fun _ : Unit => a) f) =
      ∑ n ∈ Finset.range (μ.degree + 1), PowerSeries.coeff n f * coeff μ (a ^ n) := by
  rw [← PowerSeries.subst_def, PowerSeries.coeff_subst (PowerSeries.HasSubst.of_constantCoeff_zero ha),
    finsum_eq_sum_of_support_subset (s := Finset.range (μ.degree + 1))]
  · simp
  · intro n hn
    rw [Function.mem_support] at hn
    rw [Finset.coe_range, Set.mem_Iio]
    by_contra hc
    apply hn
    rw [coeff_of_lt_order, smul_zero]
    refine lt_of_lt_of_le ?_ (le_order_pow_of_constantCoeff_eq_zero n ha)
    exact_mod_cast (by omega : μ.degree < n)

theorem mvExp_eq [CharZero C] {a : MvPowerSeries τ C} (ha : constantCoeff a = 0) :
    mvExp a = subst (fun _ : Unit => a) (PowerSeries.exp C) := by
  ext μ
  rw [coeff_psubst ha]
  show ∑ k ∈ Finset.range (μ.degree + 1), coeff μ (a ^ k) / (k.factorial : C) = _
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [PowerSeries.coeff_exp]
  simp [div_eq_mul_inv, mul_comm]

theorem mvExp_zero' : mvExp (0 : MvPowerSeries σ C) = 1 := by
  classical
  ext μ
  show ∑ k ∈ Finset.range (μ.degree + 1), coeff μ ((0 : MvPowerSeries σ C) ^ k) / (k.factorial : C) = _
  rw [Finset.sum_range_succ', Finset.sum_eq_zero]
  · simp
  · intro k _
    simp

theorem coeff_subst_kill [Finite τ] (e : σ ↪ τ) (f : MvPowerSeries τ C)
    (a : τ → MvPowerSeries σ C) (ha : ∀ t, a t = killCompl e (X t)) (x : σ →₀ ℕ) :
    coeff x (subst a f) = coeff (Finsupp.embDomain e x) f := by
  classical
  have hc : ∀ t, constantCoeff (a t) = 0 := fun t => by
    rw [ha, ← coeff_zero_eq_constantCoeff_apply, coeff_killCompl, Finsupp.embDomain_zero, coeff_zero_X]
  have hs : HasSubst a := hasSubst_of_constantCoeff_zero hc
  rw [coeff_subst hs, finsum_eq_single _ (Finsupp.embDomain e x)]
  · have : (Finsupp.embDomain e x).prod (fun s n => a s ^ n) = killCompl e (monomial (Finsupp.embDomain e x) 1) := by
      rw [monomial_one_eq, map_finsuppProd]; simp only [map_pow, ha]
    rw [this, coeff_killCompl, coeff_monomial_same, smul_eq_mul, mul_one]
  · intro d hd
    have : d.prod (fun s n => a s ^ n) = killCompl e (monomial d 1) := by
      rw [monomial_one_eq, map_finsuppProd]; simp only [map_pow, ha]
    rw [this, coeff_killCompl, coeff_monomial, if_neg (Ne.symm hd), smul_zero]

theorem pderiv_exp [CharZero C] : pderiv C () (PowerSeries.exp C) = PowerSeries.exp C := by
  refine MvPowerSeries.ext fun μ => ?_
  rw [coeff_pderiv]
  have h1 : μ = Finsupp.single () (μ ()) := Finsupp.unique_single μ
  rw [h1, ← Finsupp.single_add]
  show PowerSeries.coeff _ _ * _ = PowerSeries.coeff _ _
  simp only [PowerSeries.coeff_exp, Finsupp.single_eq_same, Nat.factorial_succ]
  have : ((μ ()).factorial : C) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  have h2 : ((μ () : C) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (μ ())
  simp
  field_simp

def tder [Fintype σ] (p w : σ → MvPowerSeries τ C) (f : MvPowerSeries σ C) : MvPowerSeries τ C :=
  ∑ s, subst p (pderiv C s f) * w s

section
variable [Fintype σ] {p : σ → MvPowerSeries τ C} (hp : ∀ s, constantCoeff (p s) = 0) (w : σ → MvPowerSeries τ C)
include hp

theorem tder_add (f g : MvPowerSeries σ C) : tder p w (f + g) = tder p w f + tder p w g := by
  simp only [tder, map_add, subst_add (hasSubst_of_constantCoeff_zero hp), add_mul, Finset.sum_add_distrib]

theorem tder_sub (f g : MvPowerSeries σ C) : tder p w (f - g) = tder p w f - tder p w g := by
  simp only [tder, map_sub, subst_sub (hasSubst_of_constantCoeff_zero hp), sub_mul, Finset.sum_sub_distrib]

theorem tder_X (s : σ) : tder p w (X s) = w s := by
  classical
  unfold tder
  rw [Finset.sum_eq_single s]
  · rw [pderiv_X_self, ← coe_substAlgHom (hasSubst_of_constantCoeff_zero hp), map_one, one_mul]
  · intro t _ ht
    rw [pderiv_X_of_ne ht.symm, subst_zero' hp, zero_mul]
  · simp

theorem tder_subst [Fintype υ] {a : υ → MvPowerSeries σ C} (ha : ∀ s, constantCoeff (a s) = 0)
    (f : MvPowerSeries υ C) :
    tder p w (subst a f) = tder (fun s => subst p (a s)) (fun s => tder p w (a s)) f := by
  unfold tder
  simp only [ReciprocityTheory.ChartRestriction.G.TB.LogPf.pderiv_subst ha, subst_sum' hp, subst_mul (hasSubst_of_constantCoeff_zero hp),
    subst_subst ha hp, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

theorem subst_tder [Finite τ] {b : τ → MvPowerSeries υ C} (hb : ∀ s, constantCoeff (b s) = 0) (f : MvPowerSeries σ C) :
    subst b (tder p w f) = tder (fun s => subst b (p s)) (fun s => subst b (w s)) f := by
  unfold tder
  simp only [subst_sum' hb, subst_mul (hasSubst_of_constantCoeff_zero hb), subst_subst hp hb]

theorem int_tder (hpi : ∀ s, IntS V (p s)) (hw : ∀ s, IntS V (w s)) {f : MvPowerSeries σ C} (hf : IntS V f) :
    IntS V (tder p w f) :=
  int_sum fun s _ => int_mul (int_subst hp hpi (int_pderiv hf s)) (hw s)

theorem int_tder_of_exp [CharZero C] (hpi : ∀ s, IntS V (p s)) (hw : ∀ s, IntS V (w s)) {f : MvPowerSeries σ C}
    (hf0 : constantCoeff f = 0) (hf : IntS V (mvExp f)) (hz : subst p f = 0) : IntS V (tder p w f) := by
  have h := int_tder hp w hpi hw hf
  rw [mvExp_eq hf0, tder_subst hp w (fun _ => hf0), hz] at h
  unfold tder at h
  rw [Fintype.sum_unique, pderiv_exp, ← mvExp_eq (map_zero _), mvExp_zero', one_mul] at h
  exact h

end

theorem tder_zero [Fintype σ] (p : σ → MvPowerSeries τ C) {w : σ → MvPowerSeries τ C} (hw : ∀ s, w s = 0)
    (f : MvPowerSeries σ C) : tder p w f = 0 := by
  simp [tder, hw]

theorem pderiv_subst_eq [Fintype σ] {a : σ → MvPowerSeries τ C} (ha : ∀ s, constantCoeff (a s) = 0)
    (f : MvPowerSeries σ C) (t : τ) : pderiv C t (subst a f) = tder a (fun s => pderiv C t (a s)) f :=
  ReciprocityTheory.ChartRestriction.G.TB.LogPf.pderiv_subst ha f t

end GlobalTheory.RowLaw.GaugeDeriv

end

noncomputable section

open scoped BigOperators
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds MvPowerSeries

namespace GlobalTheory.RowLaw.GaugeDeriv

variable {C : Type} [Field C] {V : VF C} {σ τ υ : Type}
variable {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type} [Fintype κ] {Y : RawChart C d I κ}

def pr (a b : κ → MvPowerSeries τ C) : Fin 2 × κ → MvPowerSeries τ C :=
  fun p => if p.1 = 0 then a p.2 else b p.2

def tr (a b c : κ → MvPowerSeries τ C) : Fin 3 × κ → MvPowerSeries τ C :=
  fun p => ![a, b, c] p.1 p.2

omit [Fintype κ] in
theorem pr_prop {P : MvPowerSeries τ C → Prop} {a b : κ → MvPowerSeries τ C} (ha : ∀ i, P (a i))
    (hb : ∀ i, P (b i)) : ∀ p, P (pr a b p) := by
  intro p
  unfold pr
  split_ifs
  · exact ha _
  · exact hb _

omit [Fintype κ] in
theorem tr_prop {P : MvPowerSeries τ C → Prop} {a b c : κ → MvPowerSeries τ C} (ha : ∀ i, P (a i))
    (hb : ∀ i, P (b i)) (hc : ∀ i, P (c i)) : ∀ p, P (tr a b c p) := by
  rintro ⟨j, i⟩
  fin_cases j
  · exact ha _
  · exact hb _
  · exact hc _

omit [Fintype κ] in
theorem map_pr (F : MvPowerSeries τ C → MvPowerSeries υ C) (a b : κ → MvPowerSeries τ C) :
    (fun p => F (pr a b p)) = pr (fun i => F (a i)) (fun i => F (b i)) := by
  funext p
  unfold pr
  split_ifs <;> rfl

omit [∀ g, Fintype (I g)] [Fintype κ] in
theorem hAt_eq (a b : κ → MvPowerSeries τ C) : hAt Y a b = subst (pr a b) Y.h := rfl

omit [Fintype κ] in
theorem cc_gp {n : ℕ} (j : Fin n) (i : κ) : constantCoeff (gp C κ j i) = 0 := constantCoeff_X _

def invF (Y : RawChart C d I κ) (v : κ → C) (y : κ → MvPowerSeries τ C) : κ → MvPowerSeries τ C :=
  fun i => tder (fun x => subst y (Y.lg x)) (fun x => MvPowerSeries.C (v x)) (Y.ex i)

section
variable (R : RLaw Y V)
include R

theorem cc_lg (i : κ) : constantCoeff (Y.lg i) = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply, R.lin i 0 (by simp), coeff_zero_X]

theorem cc_h : constantCoeff Y.h = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply]
  exact R.axes 0 0 (by simp)

theorem cc_slg {a : κ → MvPowerSeries τ C} (ha : ∀ i, constantCoeff (a i) = 0) (x : κ) :
    constantCoeff (subst a (Y.lg x)) = 0 := constantCoeff_subst_zero ha (cc_lg R x)

theorem cc_hAt {a b : κ → MvPowerSeries τ C} (ha : ∀ i, constantCoeff (a i) = 0)
    (hb : ∀ i, constantCoeff (b i) = 0) : constantCoeff (hAt Y a b) = 0 :=
  constantCoeff_subst_zero (pr_prop (P := fun f => constantCoeff f = 0) ha hb) (cc_h R)

theorem cc_addP {a b : κ → MvPowerSeries τ C} (ha : ∀ i, constantCoeff (a i) = 0)
    (hb : ∀ i, constantCoeff (b i) = 0) (i : κ) : constantCoeff (addP Y a b i) = 0 :=
  constantCoeff_subst_zero (fun x => by rw [map_add, cc_slg R ha, cc_slg R hb, add_zero]) (R.exc i)

theorem ex_lg {a : κ → MvPowerSeries τ C} (ha : ∀ i, constantCoeff (a i) = 0) (i : κ) :
    subst (fun x => subst a (Y.lg x)) (Y.ex i) = a i := by
  rw [← subst_subst (cc_lg R) ha, R.exlg, subst_X (hasSubst_of_constantCoeff_zero ha)]

theorem lg_ex {a : κ → MvPowerSeries τ C} (ha : ∀ i, constantCoeff (a i) = 0) (i : κ) :
    subst (fun x => subst a (Y.ex x)) (Y.lg i) = a i := by
  rw [← subst_subst R.exc ha, R.lgex, subst_X (hasSubst_of_constantCoeff_zero ha)]

theorem lg_addP {a b : κ → MvPowerSeries τ C} (ha : ∀ i, constantCoeff (a i) = 0)
    (hb : ∀ i, constantCoeff (b i) = 0) (x : κ) :
    subst (addP Y a b) (Y.lg x) = subst a (Y.lg x) + subst b (Y.lg x) :=
  lg_ex R (a := fun x => subst a (Y.lg x) + subst b (Y.lg x))
    (fun x => by rw [map_add, cc_slg R ha, cc_slg R hb, add_zero]) x

theorem subst_addP [Finite τ] {a b : κ → MvPowerSeries τ C} (ha : ∀ i, constantCoeff (a i) = 0)
    (hb : ∀ i, constantCoeff (b i) = 0) {p : τ → MvPowerSeries υ C} (hp : ∀ s, constantCoeff (p s) = 0) (i : κ) :
    subst p (addP Y a b i) = addP Y (fun i => subst p (a i)) (fun i => subst p (b i)) i := by
  unfold addP
  rw [subst_subst (fun x => by rw [map_add, cc_slg R ha, cc_slg R hb, add_zero]) hp]
  simp only [subst_add (hasSubst_of_constantCoeff_zero hp), subst_subst ha hp, subst_subst hb hp]

theorem lg_zero (x : κ) : subst (fun _ : κ => (0 : MvPowerSeries τ C)) (Y.lg x) = 0 := by
  ext μ
  exact Van.subst (T := ∅) Set.univ (fun _ => map_zero _) (fun _ _ ν _ => by simp) (van_univ (cc_lg R x)) μ
    (by simp)

theorem addP_zero {a : κ → MvPowerSeries τ C} (ha : ∀ i, constantCoeff (a i) = 0) :
    addP Y a (fun _ => 0) = a := by
  funext i
  unfold addP
  simp only [lg_zero R, add_zero]
  exact ex_lg R ha i

theorem hAt_zero_right {a : κ → MvPowerSeries τ C} (ha : ∀ i, constantCoeff (a i) = 0) :
    hAt Y a (fun _ => 0) = 0 := by
  ext μ
  refine Van.subst (T := ∅) {p : Fin 2 × κ | p.1 = 1} (pr_prop (P := fun f => constantCoeff f = 0) ha fun _ => map_zero _)
    (fun s hs ν _ => ?_) (R.axes 1) μ (by simp)
  have hs' : s.1 = 1 := hs
  simp [pr, hs']

theorem hAt_zero_left {a : κ → MvPowerSeries τ C} (ha : ∀ i, constantCoeff (a i) = 0) :
    hAt Y (fun _ => 0) a = 0 := by
  ext μ
  refine Van.subst (T := ∅) {p : Fin 2 × κ | p.1 = 0} (pr_prop (P := fun f => constantCoeff f = 0) (fun _ => map_zero _) ha)
    (fun s hs ν _ => ?_) (R.axes 0) μ (by simp)
  have hs' : s.1 = 0 := hs
  simp [pr, hs']

theorem tder_lg_zero (v : κ → C) (x : κ) :
    tder (fun _ : κ => (0 : MvPowerSeries τ C)) (fun i => MvPowerSeries.C (v i)) (Y.lg x) = MvPowerSeries.C (v x) := by
  classical
  have h1 : ∀ s, subst (fun _ : κ => (0 : MvPowerSeries τ C)) (pderiv C s (Y.lg x)) = if s = x then 1 else 0 := by
    intro s
    have h2 : constantCoeff (pderiv C s (Y.lg x - X x)) = 0 := by
      rw [← coeff_zero_eq_constantCoeff_apply, coeff_pderiv, map_sub, R.lin x _ (by simp), sub_self, zero_mul]
    have h3 : subst (fun _ : κ => (0 : MvPowerSeries τ C)) (pderiv C s (Y.lg x - X x)) = 0 := by
      ext μ
      exact Van.subst (T := ∅) Set.univ (fun _ => map_zero _) (fun _ _ ν _ => by simp) (van_univ h2) μ (by simp)
    have hs : HasSubst (fun _ : κ => (0 : MvPowerSeries τ C)) := hasSubst_of_constantCoeff_zero fun _ => map_zero _
    rw [map_sub, subst_sub hs, sub_eq_zero] at h3
    rw [h3]
    split_ifs with h
    · rw [h, pderiv_X_self, ← coe_substAlgHom hs, map_one]
    · rw [pderiv_X_of_ne (Ne.symm h), subst_zero' fun _ => map_zero _]
  simp [tder, h1]

end

theorem subst_hAt [Finite τ] {a b : κ → MvPowerSeries τ C} (ha : ∀ i, constantCoeff (a i) = 0)
    (hb : ∀ i, constantCoeff (b i) = 0) {p : τ → MvPowerSeries υ C} (hp : ∀ s, constantCoeff (p s) = 0) :
    subst p (hAt Y a b) = hAt Y (fun i => subst p (a i)) (fun i => subst p (b i)) := by
  rw [hAt_eq, subst_subst (pr_prop (P := fun f => constantCoeff f = 0) ha hb) hp, map_pr, hAt_eq]

theorem tder_hAt [Fintype τ] {a b : κ → MvPowerSeries τ C} (ha : ∀ i, constantCoeff (a i) = 0)
    (hb : ∀ i, constantCoeff (b i) = 0) {p : τ → MvPowerSeries υ C} (hp : ∀ s, constantCoeff (p s) = 0)
    (w : τ → MvPowerSeries υ C) :
    tder p w (hAt Y a b) = tder (pr (fun i => subst p (a i)) (fun i => subst p (b i)))
      (pr (fun i => tder p w (a i)) (fun i => tder p w (b i))) Y.h := by
  rw [hAt_eq, tder_subst hp w (pr_prop (P := fun f => constantCoeff f = 0) ha hb), map_pr, map_pr]

theorem sg_eq (v : κ → C) : Y.sg v = -∑ i, v i • subst (pr (X : κ → MvPowerSeries κ C) fun _ => 0)
    (pderiv C ((1 : Fin 2), i) Y.h) := by
  classical
  let e : κ ↪ Fin 2 × κ := ⟨fun x => (0, x), fun x y h => (Prod.mk.inj h).2⟩
  have he : ∀ t, (pr (X : κ → MvPowerSeries κ C) fun _ => 0) t = killCompl e (X t) := by
    rintro ⟨j, i⟩
    fin_cases j
    · exact (killCompl_X (e := e) i).symm
    · show (0 : MvPowerSeries κ C) = _
      rw [killCompl_X_eq_zero]
      rintro ⟨x, hx⟩
      exact absurd (congrArg Prod.fst hx) (show ¬ (0 : Fin 2) = 1 by decide)
  ext μ
  rw [map_neg, map_sum]
  show -∑ i, v i * coeff (μ.mapDomain (fun x : κ => ((0 : Fin 2), x)) + Finsupp.single ((1 : Fin 2), i) 1) Y.h = _
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [coeff_smul, coeff_subst_kill e _ _ he, coeff_pderiv, Finsupp.embDomain_notin_range, Finsupp.embDomain_eq_mapDomain]
  · rw [Nat.cast_zero, zero_add, mul_one]
    rfl
  · rintro ⟨x, hx⟩
    exact absurd (congrArg Prod.fst hx) (show ¬ (0 : Fin 2) = 1 by decide)

theorem tder_sg {a : κ → MvPowerSeries τ C} (ha : ∀ i, constantCoeff (a i) = 0) (v : κ → C) :
    tder (pr a fun _ => 0) (pr (fun _ => 0) fun i => MvPowerSeries.C (v i)) Y.h = -subst a (Y.sg v) := by
  have hs := hasSubst_of_constantCoeff_zero ha
  have hX : ∀ p, constantCoeff ((pr (X : κ → MvPowerSeries κ C) fun _ => 0) p) = 0 :=
    pr_prop (P := fun f => constantCoeff f = 0) (fun _ => constantCoeff_X _) fun _ => map_zero _
  rw [sg_eq, ← coe_substAlgHom hs, map_neg, neg_neg, map_sum]
  unfold tder
  rw [Fintype.sum_prod_type, Fin.sum_univ_two, Finset.sum_eq_zero (fun i _ => by simp [pr]), zero_add]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, coe_substAlgHom hs, subst_subst hX ha, map_pr]
  simp only [subst_X hs, subst_zero' ha]
  rw [mul_comm, smul_eq_C_mul]
  rfl

end GlobalTheory.RowLaw.GaugeDeriv

end

noncomputable section

open scoped BigOperators
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds MvPowerSeries

namespace GlobalTheory.RowLaw.GaugeDeriv

variable {C : Type} [Field C] {V : VF C} {σ τ υ : Type}
variable {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type} [Fintype κ] {Y : RawChart C d I κ}

theorem subst_gp {n : ℕ} {p : Fin n × κ → MvPowerSeries τ C} (hp : ∀ s, constantCoeff (p s) = 0) (j : Fin n) :
    (fun i => subst p (gp C κ j i)) = fun i => p (j, i) :=
  funext fun _ => subst_X (hasSubst_of_constantCoeff_zero hp) _

theorem tder_gp {n : ℕ} {p : Fin n × κ → MvPowerSeries τ C} (hp : ∀ s, constantCoeff (p s) = 0)
    (w : Fin n × κ → MvPowerSeries τ C) (j : Fin n) :
    (fun i => tder p w (gp C κ j i)) = fun i => w (j, i) :=
  funext fun _ => tder_X hp w _

section
variable (R : RLaw Y V)
include R

theorem tder_addP [Fintype τ] {a b : κ → MvPowerSeries τ C} (ha : ∀ i, constantCoeff (a i) = 0)
    (hb : ∀ i, constantCoeff (b i) = 0) {p : τ → MvPowerSeries υ C} (hp : ∀ s, constantCoeff (p s) = 0)
    (w : τ → MvPowerSeries υ C) (i : κ) :
    tder p w (addP Y a b i) =
      tder (fun x => subst (fun i => subst p (a i)) (Y.lg x) + subst (fun i => subst p (b i)) (Y.lg x))
        (fun x => tder (fun i => subst p (a i)) (fun i => tder p w (a i)) (Y.lg x) +
          tder (fun i => subst p (b i)) (fun i => tder p w (b i)) (Y.lg x)) (Y.ex i) := by
  unfold addP
  rw [tder_subst hp w (fun x => by rw [map_add, cc_slg R ha, cc_slg R hb, add_zero])]
  simp only [subst_add (hasSubst_of_constantCoeff_zero hp), subst_subst ha hp, subst_subst hb hp, tder_add hp,
    tder_subst hp w ha, tder_subst hp w hb]

variable {a b : κ → MvPowerSeries τ C} (ha : ∀ i, constantCoeff (a i) = 0) (hb : ∀ i, constantCoeff (b i) = 0)
  (hai : ∀ i, IntS V (a i)) (hbi : ∀ i, IntS V (b i))
include ha hb hai hbi

theorem int_addP (i : κ) : IntS V (addP Y a b i) := by
  have hp := pr_prop (P := fun f => constantCoeff f = 0) ha hb
  have h := int_subst hp (pr_prop hai hbi) (R.addInt i)
  rw [subst_addP R (cc_gp 0) (cc_gp 1) hp, subst_gp hp, subst_gp hp] at h
  exact h

variable {v : κ → C} (hv : ∀ i, V.Ge 0 (v i))
include hv

theorem int_cocycle : IntS V (subst (addP Y a b) (Y.sg v) - subst a (Y.sg v) - subst b (Y.sg v)) := by
  haveI := R.charZero
  have hp := tr_prop (P := fun f => constantCoeff f = 0) ha hb (c := fun _ => 0) fun _ => map_zero _
  have hs := hasSubst_of_constantCoeff_zero hp
  have hA := cc_addP R (cc_gp (C := C) (κ := κ) (0 : Fin 3)) (cc_gp 1)
  have e1 : (fun i => subst (tr a b fun _ => 0) (addP Y (gp C κ (0 : Fin 3)) (gp C κ 1) i)) = addP Y a b := by
    funext i
    rw [subst_addP R (cc_gp 0) (cc_gp 1) hp, subst_gp hp, subst_gp hp]
    rfl
  have h := int_tder_of_exp hp (tr (fun _ => 0) (fun _ => 0) fun i => MvPowerSeries.C (v i))
    (tr_prop hai hbi fun _ => int_zero) (tr_prop (fun _ => int_zero) (fun _ => int_zero) fun i => int_C (hv i))
    (by rw [map_sub, map_add, cc_hAt R (cc_gp _) (cc_gp _), cc_hAt R (cc_gp _) (cc_gp _), cc_hAt R hA (cc_gp _)]; simp)
    R.ph1 (by
      rw [subst_sub hs, subst_add hs, subst_hAt (cc_gp _) (cc_gp _) hp, subst_hAt (cc_gp _) (cc_gp _) hp,
        subst_hAt hA (cc_gp _) hp, e1]
      simp only [subst_gp hp]
      show hAt Y a (fun _ => 0) + hAt Y b (fun _ => 0) - hAt Y (addP Y a b) (fun _ => 0) = 0
      rw [hAt_zero_right R ha, hAt_zero_right R hb, hAt_zero_right R (cc_addP R ha hb)]
      simp)
  have e2 : (fun i => tder (tr a b fun _ => 0) (tr (fun _ => 0) (fun _ => 0) fun i => MvPowerSeries.C (v i))
      (addP Y (gp C κ (0 : Fin 3)) (gp C κ 1) i)) = fun _ => 0 := by
    funext i
    rw [tder_addP R (cc_gp 0) (cc_gp 1) hp]
    simp only [tder_gp hp]
    refine tder_zero _ (fun x => ?_) _
    show tder _ (fun _ => 0) _ + tder _ (fun _ => 0) _ = 0
    rw [tder_zero _ (fun _ => rfl), tder_zero _ (fun _ => rfl), add_zero]
  rw [tder_sub hp, tder_add hp, tder_hAt (cc_gp _) (cc_gp _) hp, tder_hAt (cc_gp _) (cc_gp _) hp,
    tder_hAt hA (cc_gp _) hp, e1, e2] at h
  simp only [subst_gp hp, tder_gp hp] at h
  change IntS V (tder (pr a fun _ => 0) (pr (fun _ => 0) fun i => MvPowerSeries.C (v i)) Y.h +
    tder (pr b fun _ => 0) (pr (fun _ => 0) fun i => MvPowerSeries.C (v i)) Y.h -
    tder (pr (addP Y a b) fun _ => 0) (pr (fun _ => 0) fun i => MvPowerSeries.C (v i)) Y.h) at h
  rw [tder_sg ha, tder_sg hb, tder_sg (cc_addP R ha hb)] at h
  convert h using 1
  ring

theorem int_second : IntS V (subst a (Y.sg v) + tder (pr a b) (pr (fun _ => 0) (invF Y v b)) Y.h) := by
  haveI := R.charZero
  have hp := tr_prop (P := fun f => constantCoeff f = 0) ha hb (c := fun _ => 0) fun _ => map_zero _
  have hs := hasSubst_of_constantCoeff_zero hp
  have hA := cc_addP R (cc_gp (C := C) (κ := κ) (1 : Fin 3)) (cc_gp 2)
  have e1 : (fun i => subst (tr a b fun _ => 0) (addP Y (gp C κ (1 : Fin 3)) (gp C κ 2) i)) = b := by
    funext i
    rw [subst_addP R (cc_gp 1) (cc_gp 2) hp, subst_gp hp, subst_gp hp]
    exact congrFun (addP_zero R hb) i
  have h := int_tder_of_exp hp (tr (fun _ => 0) (fun _ => 0) fun i => MvPowerSeries.C (v i))
    (tr_prop hai hbi fun _ => int_zero) (tr_prop (fun _ => int_zero) (fun _ => int_zero) fun i => int_C (hv i))
    (by rw [map_sub, map_add, cc_hAt R (cc_gp _) (cc_gp _), cc_hAt R (cc_gp _) (cc_gp _), cc_hAt R (cc_gp _) hA]; simp)
    R.ph2 (by
      rw [subst_sub hs, subst_add hs, subst_hAt (cc_gp _) (cc_gp _) hp, subst_hAt (cc_gp _) (cc_gp _) hp,
        subst_hAt (cc_gp _) hA hp, e1]
      simp only [subst_gp hp]
      show hAt Y a b + hAt Y a (fun _ => 0) - hAt Y a b = 0
      rw [hAt_zero_right R ha]
      simp)
  have e2 : (fun i => tder (tr a b fun _ => 0) (tr (fun _ => 0) (fun _ => 0) fun i => MvPowerSeries.C (v i))
      (addP Y (gp C κ (1 : Fin 3)) (gp C κ 2) i)) = invF Y v b := by
    funext i
    rw [tder_addP R (cc_gp 1) (cc_gp 2) hp]
    simp only [tder_gp hp, subst_gp hp]
    show tder (fun x => subst b (Y.lg x) + subst (fun _ => 0) (Y.lg x))
      (fun x => tder b (fun _ => 0) (Y.lg x) + tder (fun _ => 0) (fun i => MvPowerSeries.C (v i)) (Y.lg x)) (Y.ex i) = _
    simp only [lg_zero R, add_zero, tder_lg_zero R, tder_zero b (fun _ => rfl), zero_add]
    rfl
  rw [tder_sub hp, tder_add hp, tder_hAt (cc_gp _) (cc_gp _) hp, tder_hAt (cc_gp _) (cc_gp _) hp,
    tder_hAt (cc_gp _) hA hp, e1, e2] at h
  simp only [subst_gp hp, tder_gp hp] at h
  change IntS V (tder (pr a b) (pr (fun _ => 0) fun _ => 0) Y.h +
    tder (pr a fun _ => 0) (pr (fun _ => 0) fun i => MvPowerSeries.C (v i)) Y.h -
    tder (pr a b) (pr (fun _ => 0) (invF Y v b)) Y.h) at h
  rw [tder_sg ha, tder_zero _ (pr_prop (P := fun f => f = 0) (fun _ => rfl) fun _ => rfl)] at h
  convert int_neg h using 1
  ring

theorem int_first : IntS V (subst b (Y.sg v) + tder (pr a b) (pr (invF Y v a) fun _ => 0) Y.h) := by
  haveI := R.charZero
  have hp := tr_prop (P := fun f => constantCoeff f = 0) ha (b := fun _ => 0) (fun _ => map_zero _) hb
  have hs := hasSubst_of_constantCoeff_zero hp
  have hA := cc_addP R (cc_gp (C := C) (κ := κ) (0 : Fin 3)) (cc_gp 1)
  have e1 : (fun i => subst (tr a (fun _ => 0) b) (addP Y (gp C κ (0 : Fin 3)) (gp C κ 1) i)) = a := by
    funext i
    rw [subst_addP R (cc_gp 0) (cc_gp 1) hp, subst_gp hp, subst_gp hp]
    exact congrFun (addP_zero R ha) i
  have h := int_tder_of_exp hp (tr (fun _ => 0) (fun i => MvPowerSeries.C (v i)) fun _ => 0)
    (tr_prop hai (fun _ => int_zero) hbi) (tr_prop (fun _ => int_zero) (fun i => int_C (hv i)) fun _ => int_zero)
    (by rw [map_sub, map_add, cc_hAt R (cc_gp _) (cc_gp _), cc_hAt R (cc_gp _) (cc_gp _), cc_hAt R hA (cc_gp _)]; simp)
    R.ph1 (by
      rw [subst_sub hs, subst_add hs, subst_hAt (cc_gp _) (cc_gp _) hp, subst_hAt (cc_gp _) (cc_gp _) hp,
        subst_hAt hA (cc_gp _) hp, e1]
      simp only [subst_gp hp]
      show hAt Y a b + hAt Y (fun _ => 0) b - hAt Y a b = 0
      rw [hAt_zero_left R hb]
      simp)
  have e2 : (fun i => tder (tr a (fun _ => 0) b) (tr (fun _ => 0) (fun i => MvPowerSeries.C (v i)) fun _ => 0)
      (addP Y (gp C κ (0 : Fin 3)) (gp C κ 1) i)) = invF Y v a := by
    funext i
    rw [tder_addP R (cc_gp 0) (cc_gp 1) hp]
    simp only [tder_gp hp, subst_gp hp]
    show tder (fun x => subst a (Y.lg x) + subst (fun _ => 0) (Y.lg x))
      (fun x => tder a (fun _ => 0) (Y.lg x) + tder (fun _ => 0) (fun i => MvPowerSeries.C (v i)) (Y.lg x)) (Y.ex i) = _
    simp only [lg_zero R, add_zero, tder_lg_zero R, tder_zero a (fun _ => rfl), zero_add]
    rfl
  rw [tder_sub hp, tder_add hp, tder_hAt (cc_gp _) (cc_gp _) hp, tder_hAt (cc_gp _) (cc_gp _) hp,
    tder_hAt hA (cc_gp _) hp, e1, e2] at h
  simp only [subst_gp hp, tder_gp hp] at h
  change IntS V (tder (pr a b) (pr (fun _ => 0) fun _ => 0) Y.h +
    tder (pr (fun _ => 0) b) (pr (fun i => MvPowerSeries.C (v i)) fun _ => 0) Y.h -
    tder (pr a b) (pr (invF Y v a) fun _ => 0) Y.h) at h
  rw [tder_zero _ (pr_prop (P := fun f => f = 0) (fun _ => rfl) fun _ => rfl)] at h
  have hq := pr_prop (P := fun f => constantCoeff f = 0) (a := fun _ => 0) (fun _ => map_zero _) hb
  have h' := int_tder_of_exp hq (pr (fun i => MvPowerSeries.C (v i)) fun _ => 0)
    (pr_prop (fun _ => int_zero) hbi) (pr_prop (fun i => int_C (hv i)) fun _ => int_zero)
    (by rw [map_sub, cc_hAt R (cc_gp _) (cc_gp _), cc_h R]; simp) R.sy (by
      rw [subst_sub (hasSubst_of_constantCoeff_zero hq), subst_hAt (cc_gp _) (cc_gp _) hq, ← hAt_eq]
      simp only [subst_gp hq]
      show hAt Y b (fun _ => 0) - hAt Y (fun _ => 0) b = 0
      rw [hAt_zero_left R hb, hAt_zero_right R hb, sub_zero])
  rw [tder_sub hq, tder_hAt (cc_gp _) (cc_gp _) hq] at h'
  simp only [subst_gp hq, tder_gp hq] at h'
  change IntS V (tder (pr b fun _ => 0) (pr (fun _ => 0) fun i => MvPowerSeries.C (v i)) Y.h - _) at h'
  rw [tder_sg hb] at h'
  convert int_neg (int_add h h') using 1
  ring

end

end GlobalTheory.RowLaw.GaugeDeriv

end

noncomputable section

open scoped BigOperators
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds MvPowerSeries

namespace GlobalTheory.RowLaw.GaugeDeriv

variable {C : Type} [Field C] {V : VF C} {σ τ υ : Type}
variable {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type} [Fintype κ] {Y : RawChart C d I κ}

theorem subst_origin [Finite σ] {f : MvPowerSeries σ C} (hf : constantCoeff f = 0) :
    subst (fun _ : σ => (0 : MvPowerSeries τ C)) f = 0 := by
  ext μ
  exact Van.subst (T := ∅) Set.univ (fun _ => map_zero _) (fun _ _ ν _ => by simp) (van_univ hf) μ (by simp)

theorem exists_sum (R : RLaw Y V) {ι : Type} (s : Finset ι) (b : ι → κ → MvPowerSeries τ C)
    (hb : ∀ c i, constantCoeff (b c i) = 0) (hbi : ∀ c i, IntS V (b c i)) :
    ∃ P : κ → MvPowerSeries τ C, (∀ i, constantCoeff (P i) = 0) ∧ (∀ i, IntS V (P i)) ∧
      (∀ x, subst P (Y.lg x) = ∑ c ∈ s, subst (b c) (Y.lg x)) ∧
      ∀ v : κ → C, (∀ i, V.Ge 0 (v i)) → IntS V (subst P (Y.sg v) - ∑ c ∈ s, subst (b c) (Y.sg v)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨fun _ => 0, fun _ => map_zero _, fun _ => int_zero, fun x => by simpa using lg_zero R x, fun v _ => ?_⟩
    rw [subst_origin (Y.constantCoeff_sg (R.axes 0) v)]
    simpa using int_zero
  | insert c s hc ih =>
    obtain ⟨P, h0, hi, hl, hs⟩ := ih
    refine ⟨addP Y (b c) P, cc_addP R (hb c) h0, int_addP R (hb c) h0 (hbi c) hi, fun x => ?_, fun v hv => ?_⟩
    · rw [lg_addP R (hb c) h0, hl, Finset.sum_insert hc]
    · rw [Finset.sum_insert hc]
      convert int_add (int_cocycle R (hb c) h0 (hbi c) hi hv) (hs v hv) using 1
      ring

theorem coeff_subst_tyS {l : ℕ} (hl : 2 ≤ l) {a : MvPowerSeries τ C} (ha : constantCoeff a = 0) (x : ℕ → C)
    (μ : τ →₀ ℕ) : coeff μ (subst (fun _ : Unit => a) (tyS l x)) =
      ∑ s ∈ Finset.range (μ.degree + 1), x s * coeff μ (a ^ (l ^ s)) := by
  rw [coeff_psubst ha]
  have h1 : ∀ n ∈ Finset.range (μ.degree + 1), PowerSeries.coeff n (tyS l x) * coeff μ (a ^ n) =
      ∑ s ∈ Finset.range (μ.degree + 1), if l ^ s = n then x s * coeff μ (a ^ (l ^ s)) else 0 := by
    intro n hn
    by_cases h : ∃ s, l ^ s = n
    · obtain ⟨s, rfl⟩ := h
      rw [coeff_tyS_pow hl, Finset.sum_eq_single s, if_pos rfl]
      · intro s' _ hs'
        exact if_neg fun h => hs' (Nat.pow_right_injective hl h)
      · intro hs
        exfalso
        apply hs
        have : s < l ^ s := Nat.lt_pow_self (by omega)
        rw [Finset.mem_range] at hn ⊢
        omega
    · push Not at h
      rw [coeff_tyS_of_ne x n h, zero_mul, Finset.sum_eq_zero fun s _ => if_neg (h s)]
  rw [Finset.sum_congr rfl h1, Finset.sum_comm]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Finset.sum_ite_eq]
  split_ifs with h
  · rfl
  · rw [coeff_of_lt_order, mul_zero]
    refine lt_of_lt_of_le ?_ (le_order_pow_of_constantCoeff_eq_zero _ ha)
    rw [Finset.mem_range] at h
    exact_mod_cast (by omega : μ.degree < l ^ s)

section
variable {I₁ J₁ : Type} [Fintype I₁] [Fintype J₁] {G : Cart V d I₁ J₁} (S : Sys G) {t : I₁ → MvPowerSeries I₁ C}
  (ht : S.IsT t)
include ht

theorem sum_lie (y : I₁) :
    ∑ c, subst (fun _ : Unit => t c) (tyS V.l fun s => S.cur c s (Sum.inl y)) = (X y : MvPowerSeries I₁ C) := by
  classical
  ext μ
  rw [map_sum]
  simp only [coeff_subst_tyS V.l_prime.two_le (ht.1 _)]
  rw [Finset.sum_comm, coeff_X]
  convert ht.2 y μ
  rfl

theorem sum_fil (q : J₁) :
    ∑ c, subst (fun _ : Unit => t c) (tyS V.l fun s => S.cur c s (Sum.inr q)) = -S.ze t q := by
  classical
  ext μ
  rw [map_sum, map_neg]
  simp only [coeff_subst_tyS V.l_prime.two_le (ht.1 _)]
  rw [Finset.sum_comm]
  show _ = -(-(∑ s ∈ Finset.Icc 1 μ.degree, ∑ c, S.be c s q * coeff μ (t c ^ (V.l ^ s))))
  rw [neg_neg]
  symm
  refine Finset.sum_subset (fun s hs => ?_) fun s hs hs' => ?_
  · rw [Finset.mem_Icc] at hs
    rw [Finset.mem_range]
    omega
  · rw [Finset.mem_Icc] at hs'
    rw [Finset.mem_range] at hs
    have : s = 0 := by omega
    subst this
    refine Finset.sum_eq_zero fun c _ => ?_
    rw [Sys.be, (S.curve c).2.1]
    simp

end

theorem group_point (R : RLaw Y V) {g : Fin 2} {H : Y.CartHyp V g} (S : Sys (RawChart.cart H))
    {t : I g → MvPowerSeries (I g) C} (ht : S.IsT t) {Θ : WV I → MvPowerSeries (WV I) C}
    (hΘ0 : ∀ w, constantCoeff (Θ w) = 0) (hΘ : ∀ c, Θ ⟨g, c⟩ = upG g (t c)) :
    ∃ P : κ → MvPowerSeries (WV I) C, (∀ i, constantCoeff (P i) = 0) ∧ (∀ i, IntS V (P i)) ∧
      (∀ i, subst Θ (P i) = Y.expPt g i) ∧
      ∀ q : JJ I g, ∃ J, IntS V J ∧ subst Θ (subst P (Y.sg (Y.u (1 - g) q))) = subst Θ J + upG g (S.ze t q) +
        ∑ y : I g, (if Y.ty g y = Y.ty (1 - g) q then Y.sg1 (Y.u g y) (Y.u (1 - g) q) else 0) •
          (X (⟨g, y⟩ : WV I) : MvPowerSeries (WV I) C) := by
  classical
  have hc : ∀ c, S.cur c ∈ Y.TySet V g := fun c => (S.curve c).1
  choose γ lam hγ hlam h1 h2 using hc
  have hX : ∀ c : I g, ∀ _ : Unit, constantCoeff (X (⟨g, c⟩ : WV I) : MvPowerSeries (WV I) C) = 0 :=
    fun _ _ => constantCoeff_X _
  have hU : ∀ c : I g, constantCoeff (X (⟨g, c⟩ : WV I) : MvPowerSeries (WV I) C) = 0 := fun _ => constantCoeff_X _
  have hsU := hasSubst_of_constantCoeff_zero hU
  have hsΘ := hasSubst_of_constantCoeff_zero hΘ0
  have hst : ∀ c, HasSubst fun _ : Unit => t c := fun c => hasSubst_of_constantCoeff_zero fun _ => ht.1 c
  have hint : ∀ (c : I g) (f : PowerSeries C), (∀ n, V.Ge 0 (PowerSeries.coeff n f)) →
      IntS V (subst (fun _ : Unit => (X (⟨g, c⟩ : WV I) : MvPowerSeries (WV I) C)) f) := by
    intro c f hf
    refine int_subst (hX c) (fun _ => int_X _) fun μ => ?_
    rw [Finsupp.unique_single μ]
    exact hf _
  obtain ⟨P, h0, hi, hl, hs⟩ := exists_sum R Finset.univ
    (fun c i => subst (fun _ : Unit => (X (⟨g, c⟩ : WV I) : MvPowerSeries (WV I) C)) (γ c i))
    (fun c i => constantCoeff_subst_zero (hX c) (hγ c i).1) (fun c i => hint c _ (hγ c i).2)
  have k1 : ∀ (c : I g) (f : PowerSeries C),
      subst Θ (subst (fun _ : Unit => (X (⟨g, c⟩ : WV I) : MvPowerSeries (WV I) C)) f) =
        upG g (subst (fun _ : Unit => t c) f) := by
    intro c f
    rw [subst_subst (hX c) hΘ0, subst_X hsΘ, hΘ, upG, upG, subst_subst (fun _ => ht.1 c) hU]
  have k2 : ∀ (c : I g) (f : MvPowerSeries κ C),
      subst (fun i => subst (fun _ : Unit => (X (⟨g, c⟩ : WV I) : MvPowerSeries (WV I) C)) (γ c i)) f =
        subst (fun _ : Unit => (X (⟨g, c⟩ : WV I) : MvPowerSeries (WV I) C)) (alongCv (γ c) f) :=
    fun c f => (subst_subst (fun i => (hγ c i).1) (hX c) f).symm
  have k3 : ∀ b : I g → C, ∑ c, upG g (subst (fun _ : Unit => t c)
      (∑ y, b y • tyS V.l fun s => S.cur c s (Sum.inl y))) =
      ∑ y, b y • (X (⟨g, y⟩ : WV I) : MvPowerSeries (WV I) C) := by
    intro b
    unfold upG
    rw [← subst_sum' hU]
    have : ∀ c, subst (fun _ : Unit => t c) (∑ y, b y • tyS V.l fun s => S.cur c s (Sum.inl y)) =
        ∑ y, b y • subst (fun _ : Unit => t c) (tyS V.l fun s => S.cur c s (Sum.inl y)) := by
      intro c
      rw [subst_sum' (fun _ => ht.1 c)]
      exact Finset.sum_congr rfl fun y _ => subst_smul (hst c) _ _
    simp only [this]
    rw [Finset.sum_comm]
    simp only [← Finset.smul_sum, sum_lie S ht]
    rw [subst_sum' hU]
    exact Finset.sum_congr rfl fun y _ => by rw [subst_smul hsU, subst_X hsU]
  refine ⟨P, h0, hi, fun i => ?_, fun q => ?_⟩
  · rw [← ex_lg R (a := fun i => subst Θ (P i)) (fun i => constantCoeff_subst_zero hΘ0 (h0 i)) i]
    unfold RawChart.expPt
    congr 1
    funext x
    rw [← subst_subst h0 hΘ0, hl, subst_sum' hΘ0]
    simp only [k2, k1, h1, k3]
  · refine ⟨_, int_add (hs _ (R.uint (1 - g) q)) (int_sum (s := Finset.univ) fun c _ => hint c _ (hlam c q).2), ?_⟩
    have h3 : ∀ c, alongCv (γ c) (Y.sg (Y.u (1 - g) q)) = lam c q - (tyS V.l fun s => S.cur c s (Sum.inr q)) +
        ∑ y, (if Y.ty g y = Y.ty (1 - g) q then Y.sg1 (Y.u g y) (Y.u (1 - g) q) else 0) •
          tyS V.l fun s => S.cur c s (Sum.inl y) := by
      intro c
      rw [h2 c q]
      simp only [ite_smul, zero_smul]
      abel
    have h4 : upG g (S.ze t q) = -∑ c, upG g (subst (fun _ : Unit => t c) (tyS V.l fun s => S.cur c s (Sum.inr q))) := by
      unfold upG
      rw [← subst_sum' hU, sum_fil S ht, ← coe_substAlgHom hsU, map_neg, neg_neg]
    have h5 : ∀ c, upG g (subst (fun _ : Unit => t c) (alongCv (γ c) (Y.sg (Y.u (1 - g) q)))) =
        upG g (subst (fun _ : Unit => t c) (lam c q)) -
        upG g (subst (fun _ : Unit => t c) (tyS V.l fun s => S.cur c s (Sum.inr q))) +
        upG g (subst (fun _ : Unit => t c) (∑ y, (if Y.ty g y = Y.ty (1 - g) q then
          Y.sg1 (Y.u g y) (Y.u (1 - g) q) else 0) • tyS V.l fun s => S.cur c s (Sum.inl y))) := by
      intro c
      unfold upG
      rw [h3, subst_add (hst c), subst_sub (hst c), subst_add hsU, subst_sub hsU]
    rw [subst_add hsΘ, subst_sub hsΘ, subst_sum' hΘ0, subst_sum' hΘ0, h4, ← k3]
    simp only [k2, k1, h5, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    abel

end GlobalTheory.RowLaw.GaugeDeriv

end

noncomputable section

open scoped BigOperators
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds MvPowerSeries

namespace GlobalTheory.RowLaw.GaugeDeriv

variable {C : Type} [Field C] {V : VF C} {σ τ υ : Type}
variable {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type} [Fintype κ] {Y : RawChart C d I κ}

theorem cc_lin (g : Fin 2) (i : κ) :
    constantCoeff (∑ c : I g, Y.u g c i • (X (⟨g, c⟩ : WV I) : MvPowerSeries (WV I) C)) = 0 :=
  (RawChart.van_lin g _).const

theorem cc_expPt (R : RLaw Y V) (g : Fin 2) (i : κ) : constantCoeff (Y.expPt g i) = 0 :=
  (Y.van_expPt R.exc g i).const

theorem pderiv_expPt_self (R : RLaw Y V) (g : Fin 2) (k : I g) :
    (fun i => pderiv C (⟨g, k⟩ : WV I) (Y.expPt g i)) = invF Y (Y.u g k) (Y.expPt g) := by
  classical
  funext i
  unfold invF
  rw [RawChart.expPt, pderiv_subst_eq (cc_lin g)]
  congr 1
  · funext x
    exact (lg_ex R (cc_lin g) x).symm
  · funext x
    rw [map_sum, Finset.sum_eq_single k, Derivation.map_smul, pderiv_X_self, smul_eq_C_mul, mul_one]
    · intro c _ hc
      rw [Derivation.map_smul, pderiv_X_of_ne, smul_zero]
      intro h
      exact hc (eq_of_heq (Sigma.mk.inj h).2)
    · simp

theorem pderiv_expPt_ne {g g' : Fin 2} (hg : g ≠ g') (k : I g') :
    (fun i => pderiv C (⟨g', k⟩ : WV I) (Y.expPt g i)) = fun _ => 0 := by
  funext i
  rw [RawChart.expPt, pderiv_subst_eq (cc_lin g)]
  refine tder_zero _ (fun x => ?_) _
  rw [map_sum]
  refine Finset.sum_eq_zero fun c _ => ?_
  rw [Derivation.map_smul, pderiv_X_of_ne, smul_zero]
  intro h
  exact hg (Sigma.mk.inj h).1

theorem subst_invF (R : RLaw Y V) [Finite τ] {a : κ → MvPowerSeries τ C} (ha : ∀ i, constantCoeff (a i) = 0)
    {p : τ → MvPowerSeries υ C} (hp : ∀ s, constantCoeff (p s) = 0) (v : κ → C) :
    (fun i => subst p (invF Y v a i)) = invF Y v fun i => subst p (a i) := by
  funext i
  unfold invF
  rw [subst_tder (cc_slg R ha) _ hp]
  simp only [subst_subst ha hp, subst_C]

theorem pderiv_gauge (R : RLaw Y V) {Θ : WV I → MvPowerSeries (WV I) C} (hΘ0 : ∀ w, constantCoeff (Θ w) = 0)
    {P : Fin 2 → κ → MvPowerSeries (WV I) C} (h0 : ∀ g i, constantCoeff (P g i) = 0) (hi : ∀ g i, IntS V (P g i))
    (hP : ∀ g i, subst Θ (P g i) = Y.expPt g i) {g g' : Fin 2} (hg : g ≠ g') (k : I g') :
    ∃ J, IntS V J ∧ pderiv C (⟨g', k⟩ : WV I) (subst (fun p : Fin 2 × κ => Y.expPt p.1 p.2) Y.h) =
      subst Θ J - subst Θ (subst (P g) (Y.sg (Y.u g' k))) := by
  have hsΘ := hasSubst_of_constantCoeff_zero hΘ0
  have e : (fun p : Fin 2 × κ => Y.expPt p.1 p.2) = pr (Y.expPt 0) (Y.expPt 1) := by
    funext ⟨j, i⟩
    fin_cases j <;> rfl
  have hp := pr_prop (P := fun f => constantCoeff f = 0) (h0 0) (h0 1)
  have hP' : ∀ g, (fun i => subst Θ (P g i)) = Y.expPt g := fun g => funext (hP g)
  rw [e, pderiv_subst_eq (pr_prop (P := fun f => constantCoeff f = 0) (cc_expPt R 0) (cc_expPt R 1)), map_pr]
  have hcase : (g = 0 ∧ g' = 1) ∨ (g = 1 ∧ g' = 0) := by
    clear * - hg
    revert g g'
    decide
  rcases hcase with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · refine ⟨_, int_second R (h0 0) (h0 1) (hi 0) (hi 1) (R.uint 1 k), ?_⟩
    rw [subst_add hsΘ, subst_tder hp _ hΘ0, map_pr, map_pr, subst_invF R (h0 1) hΘ0, hP', hP',
      pderiv_expPt_self R, pderiv_expPt_ne hg]
    simp only [subst_zero' hΘ0]
    ring
  · refine ⟨_, int_first R (h0 0) (h0 1) (hi 0) (hi 1) (R.uint 0 k), ?_⟩
    rw [subst_add hsΘ, subst_tder hp _ hΘ0, map_pr, map_pr, subst_invF R (h0 0) hΘ0, hP', hP',
      pderiv_expPt_self R, pderiv_expPt_ne hg]
    simp only [subst_zero' hΘ0]
    ring

end GlobalTheory.RowLaw.GaugeDeriv

namespace GlobalTheory.RowLaw

open GaugeDeriv

theorem cEqSt_of_rLaw (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (I : Fin 2 → Type) [∀ g, Fintype (I g)]
    (κ : Type) [Fintype κ] (Y : RawChart C d I κ) (R : RLaw Y V) (H : ∀ g, Y.CartHyp V g) : RawChart.CEqSt H := by
  classical
  intro _ g a a' hodd S t ht k hk
  have hne : a' ≠ a := by
    rintro rfl
    simp at hodd
  have hg : g ≠ 1 - g := by
    clear * -
    revert g
    decide
  have hΘ0 : ∀ w : WV I, constantCoeff (upG w.1 (t w.1 w.2)) = 0 := fun w =>
    constantCoeff_subst_zero (fun _ => constantCoeff_X _) ((ht w.1).1 w.2)
  have hsΘ := hasSubst_of_constantCoeff_zero hΘ0
  choose P h0 hi hP hσ using fun g => group_point R (S g) (ht g) hΘ0 (fun _ => rfl)
  obtain ⟨J₁, hJ₁, e₁⟩ := pderiv_gauge R hΘ0 h0 hi hP hg k
  obtain ⟨J₂, hJ₂, e₂⟩ := hσ g k
  refine ⟨_, ⟨(Y.k : C) • (J₁ - J₂), int_smul (VF.ge_natCast _) (int_sub hJ₁ hJ₂), rfl⟩, ?_⟩
  have e₃ : ∑ q : JJ I g, Y.pairK g q k • upG g ((S g).ze (t g) q) = -((Y.k : C) • upG g ((S g).ze (t g) k)) := by
    rw [Finset.sum_eq_single k]
    · simp [RawChart.pairK]
    · intro q _ hq
      simp [RawChart.pairK, hq]
    · simp
  have hk' : Y.OnLf g a a' ⟨1 - g, k⟩ := Or.inr ⟨rfl, hk⟩
  rw [e₃]
  ext μ
  rw [map_sub]
  have hsupp : (∀ w ∈ (μ + Finsupp.single (⟨1 - g, k⟩ : WV I) 1).support, Y.OnLf g a a' w) ↔
      ∀ w ∈ μ.support, Y.OnLf g a a' w := by
    constructor
    · intro h w hw
      apply h
      rw [Finsupp.mem_support_iff] at hw ⊢
      rw [Finsupp.add_apply]
      omega
    · intro h w hw
      rcases Finset.mem_union.1 (Finsupp.support_add hw) with h' | h'
      · exact h w h'
      · rw [Finset.mem_singleton.1 (Finsupp.support_single_subset h')]
        exact hk'
  have hL : ∀ F : MvPowerSeries (WV I) C, coeff μ (toLeaf (fun g => RawChart.cart (H g)) g a a' F) =
      if ∀ w ∈ μ.support, Y.OnLf g a a' w then coeff μ F else 0 := fun F => by
    show (if ∀ w ∈ μ.support, OnLeafV (fun g => RawChart.cart (H g)) g a a' w then coeff μ F else 0) = _
    congr
  have hD : coeff μ (dVar (⟨1 - g, k⟩ : WV I) (Y.hLf g a a')) =
      if ∀ w ∈ μ.support, Y.OnLf g a a' w then coeff μ (pderiv C (⟨1 - g, k⟩ : WV I) Y.hRow) else 0 := by
    show ((μ ⟨1 - g, k⟩ + 1 : ℕ) : C) * Y.hLf g a a' (μ + Finsupp.single (⟨1 - g, k⟩ : WV I) 1) = _
    unfold RawChart.hLf
    by_cases h : ∀ w ∈ μ.support, Y.OnLf g a a' w
    · rw [if_pos h, if_pos (hsupp.2 h), coeff_pderiv, mul_comm]
      push_cast
      rfl
    · rw [if_neg h, if_neg (fun h' => h (hsupp.1 h')), mul_zero]
  rw [hD, hL, hL]
  split_ifs with h
  · have hz : coeff μ (∑ y : I g, (if Y.ty g y = Y.ty (1 - g) k then Y.sg1 (Y.u g y) (Y.u (1 - g) k) else 0) •
        (X (⟨g, y⟩ : WV I) : MvPowerSeries (WV I) C)) = 0 := by
      rw [map_sum]
      refine Finset.sum_eq_zero fun y _ => ?_
      rw [coeff_smul, coeff_X]
      split_ifs with h1 h2
      · exfalso
        rcases h ⟨g, y⟩ (by rw [h2]; simp) with h3 | h3
        · exact hne (hk.symm.trans (h1.symm.trans h3.2))
        · exact hg h3.1
      · exact mul_zero _
      · exact zero_mul _
      · exact zero_mul _
    rw [RawChart.hRow, Derivation.map_smul, e₁, e₂, subst_smul hsΘ, subst_sub hsΘ]
    simp only [coeff_smul, map_sub, map_add, map_neg, hz]
    ring
  · exact sub_zero _

end GlobalTheory.RowLaw
