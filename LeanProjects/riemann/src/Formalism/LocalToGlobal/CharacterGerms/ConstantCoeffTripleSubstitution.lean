import Formalism.LocalToGlobal.CharacterGerms.RowTieValU

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj

namespace VP

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {τ : Type}

def P2 (a b : Fin dd → MvPowerSeries τ C) : Fin 2 × Fin dd → MvPowerSeries τ C :=
  fun q => if q.1 = 0 then a q.2 else b q.2

def P3 (a b c : Fin dd → MvPowerSeries τ C) : Fin 3 × Fin dd → MvPowerSeries τ C :=
  fun q => if q.1 = 0 then a q.2 else if q.1 = 1 then b q.2 else c q.2

theorem constantCoeff_pair_substitution {a b : Fin dd → MvPowerSeries τ C} (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0)
    (hb : ∀ i, MvPowerSeries.constantCoeff (b i) = 0) (q : Fin 2 × Fin dd) :
    MvPowerSeries.constantCoeff (P2 a b q) = 0 := by
  unfold P2
  split_ifs
  exacts [ha _, hb _]

theorem constantCoeff_triple_substitution {a b c : Fin dd → MvPowerSeries τ C} (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0)
    (hb : ∀ i, MvPowerSeries.constantCoeff (b i) = 0) (hc : ∀ i, MvPowerSeries.constantCoeff (c i) = 0)
    (q : Fin 3 × Fin dd) : MvPowerSeries.constantCoeff (P3 a b c q) = 0 := by
  unfold P3
  split_ifs
  exacts [ha _, hb _, hc _]

theorem integral_pair_substitution {a b : Fin dd → MvPowerSeries τ C} (ha : ∀ i, IntS V (a i)) (hb : ∀ i, IntS V (b i))
    (q : Fin 2 × Fin dd) : IntS V (P2 a b q) := by
  unfold P2
  split_ifs
  exacts [ha _, hb _]

theorem integral_triple_substitution {a b c : Fin dd → MvPowerSeries τ C} (ha : ∀ i, IntS V (a i)) (hb : ∀ i, IntS V (b i))
    (hc : ∀ i, IntS V (c i)) (q : Fin 3 × Fin dd) : IntS V (P3 a b c q) := by
  unfold P3
  split_ifs
  exacts [ha _, hb _, hc _]

theorem subst_sub' {σ : Type} [Finite σ] {a : σ → MvPowerSeries τ C}
    (ha : ∀ s, MvPowerSeries.constantCoeff (a s) = 0) (f g : MvPowerSeries σ C) :
    MvPowerSeries.subst a (f - g) = MvPowerSeries.subst a f - MvPowerSeries.subst a g := by
  rw [← MvPowerSeries.coe_substAlgHom (VP.hs ha)]
  exact map_sub _ f g

theorem subst_add' {σ : Type} [Finite σ] {a : σ → MvPowerSeries τ C}
    (ha : ∀ s, MvPowerSeries.constantCoeff (a s) = 0) (f g : MvPowerSeries σ C) :
    MvPowerSeries.subst a (f + g) = MvPowerSeries.subst a f + MvPowerSeries.subst a g := by
  rw [← MvPowerSeries.coe_substAlgHom (VP.hs ha)]
  exact map_add _ f g

theorem cc_pt {n : ℕ} (g : Fin n) (i : Fin dd) : MvPowerSeries.constantCoeff (pt C dd g i) = 0 := MvPowerSeries.constantCoeff_X _

theorem toK_eq {n : ℕ} (f : PS C n dd) : FB.toK C f = f := by
  unfold FB.toK
  simp

variable (Y : FBChart C V O dd)

def hAt (a b : Fin dd → MvPowerSeries τ C) : MvPowerSeries τ C := MvPowerSeries.subst (P2 a b) Y.h

def actAt (x : O) (a : Fin dd → MvPowerSeries τ C) : Fin dd → MvPowerSeries τ C :=
  fun i => MvPowerSeries.subst (fun q : Fin 1 × Fin dd => a q.2) (Y.B.A.act x i)

def addAt (a b : Fin dd → MvPowerSeries τ C) : Fin dd → MvPowerSeries τ C :=
  fun i => MvPowerSeries.subst (P2 a b) (Y.B.G.F i)

theorem cc_hAt {a b : Fin dd → MvPowerSeries τ C} (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0)
    (hb : ∀ i, MvPowerSeries.constantCoeff (b i) = 0) : MvPowerSeries.constantCoeff (hAt Y a b) = 0 := by
  unfold hAt
  exact VP.cc_subst (constantCoeff_pair_substitution ha hb) (cc_h Y)

theorem cc_actAt (x : O) {a : Fin dd → MvPowerSeries τ C} (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0)
    (i : Fin dd) : MvPowerSeries.constantCoeff (actAt Y x a i) = 0 := by
  unfold actAt
  exact VP.cc_subst (fun q : Fin 1 × Fin dd => ha q.2) (Y.B.A.const x i)

theorem int_actAt (x : O) {a : Fin dd → MvPowerSeries τ C} (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0)
    (hai : ∀ i, IntS V (a i)) (i : Fin dd) : IntS V (actAt Y x a i) := by
  unfold actAt
  exact IntS.subst (fun q : Fin 1 × Fin dd => ha q.2) (fun q : Fin 1 × Fin dd => hai q.2) (Y.intAct x i)

theorem eval_two_points_eq_subst {n m : ℕ} (a b : Pt C n dd) (f : PS C 2 dd) (_hm : m = 2) : ev ![a, b] f = MvPowerSeries.subst (P2 a b) f := by
  unfold ev
  congr 1
  funext q
  rcases q with ⟨i, k⟩
  fin_cases i <;> simp [P2]

theorem actK_eq (x : O) (i : Fin dd) : Y.B.actK C x i = Y.B.A.act x i := by
  unfold FB.actK
  exact toK_eq _

theorem compose_one_action_eq_actAt {n : ℕ} (x : O) (a : Pt C n dd) : comp1 (Y.B.actK C x) a = actAt Y x a := by
  funext i
  simp only [comp1, ev, actAt, actK_eq, Matrix.cons_val_fin_one]

variable {a b : Fin dd → MvPowerSeries τ C} (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0)
  (hb : ∀ i, MvPowerSeries.constantCoeff (b i) = 0)

include ha hb

theorem pair_subst_coordinate (g : Fin 2) (i : Fin dd) :
    MvPowerSeries.subst (P2 a b) (pt C dd g i) = P2 a b (g, i) := by
  rw [show pt C dd g i = (MvPowerSeries.X (g, i) : MvPowerSeries (Fin 2 × Fin dd) C) from rfl]
  exact VP.subst_X (constantCoeff_pair_substitution ha hb) (g, i)

theorem sy_at : MvPowerSeries.subst (P2 a b) Y.B.sy = mvExp (hAt Y b a - hAt Y a b) := by
  obtain ⟨-, -, -, -, hsy, -⟩ := Y.gauge
  rw [toK_eq] at hsy
  have hP10 : ∀ q, MvPowerSeries.constantCoeff (P2 (pt C dd 1) (pt C dd 0) q : PS C 2 dd) = 0 :=
    constantCoeff_pair_substitution (cc_pt 1) (cc_pt 0)
  have hswap : MvPowerSeries.subst (P2 a b) (ev ![pt C dd 1, pt C dd 0] Y.h) = hAt Y b a := by
    rw [eval_two_points_eq_subst (m := 2) _ _ _ rfl, VP.subst_subst hP10 (constantCoeff_pair_substitution ha hb)]
    unfold hAt
    congr 1
    funext q
    rcases q with ⟨i, k⟩
    fin_cases i
    · show MvPowerSeries.subst (P2 a b) (pt C dd 1 k) = b k
      rw [pair_subst_coordinate ha hb]
      rfl
    · show MvPowerSeries.subst (P2 a b) (pt C dd 0 k) = a k
      rw [pair_subst_coordinate ha hb]
      rfl
  have hcc : MvPowerSeries.constantCoeff (ev ![pt C dd 1, pt C dd 0] Y.h - Y.h) = 0 := by
    rw [map_sub, eval_two_points_eq_subst (m := 2) _ _ _ rfl, VP.cc_subst hP10 (cc_h Y), cc_h Y, sub_zero]
  rw [hsy, expS_eq _ hcc, subst_exp (constantCoeff_pair_substitution ha hb) hcc, subst_sub' (constantCoeff_pair_substitution ha hb), hswap]
  rfl

theorem actAt_pt (x : O) (g : Fin 2) (i : Fin dd) :
    MvPowerSeries.subst (P2 a b) (actAt Y x (pt C dd g) i) = actAt Y x (fun j => P2 a b (g, j)) i := by
  unfold actAt
  rw [VP.subst_subst (fun q : Fin 1 × Fin dd => cc_pt g q.2) (constantCoeff_pair_substitution ha hb)]
  congr 1
  funext q
  exact pair_subst_coordinate ha hb g q.2

theorem ad_at (x : O) :
    MvPowerSeries.subst (P2 a b) (Y.B.ad x) = mvExp (hAt Y (actAt Y x a) b - hAt Y a (actAt Y (star x) b)) := by
  obtain ⟨-, -, -, -, -, had⟩ := Y.gauge
  have hx := had x
  rw [toK_eq, compose_one_action_eq_actAt Y x, compose_one_action_eq_actAt Y (star x)] at hx
  have hA0 : ∀ i, MvPowerSeries.constantCoeff (actAt Y x (pt C dd 0) i : PS C 2 dd) = 0 :=
    cc_actAt Y x (cc_pt (n := 2) 0)
  have hA1 : ∀ i, MvPowerSeries.constantCoeff (actAt Y (star x) (pt C dd 1) i : PS C 2 dd) = 0 :=
    cc_actAt Y (star x) (cc_pt (n := 2) 1)
  have hQ1 : ∀ q, MvPowerSeries.constantCoeff (P2 (actAt Y x (pt C dd 0)) (pt C dd 1) q : PS C 2 dd) = 0 :=
    constantCoeff_pair_substitution hA0 (cc_pt (n := 2) 1)
  have hQ2 : ∀ q, MvPowerSeries.constantCoeff (P2 (pt C dd 0) (actAt Y (star x) (pt C dd 1)) q : PS C 2 dd) = 0 :=
    constantCoeff_pair_substitution (cc_pt (n := 2) 0) hA1
  have e1 : MvPowerSeries.subst (P2 a b) (ev ![actAt Y x (pt C dd 0), pt C dd 1] Y.h) = hAt Y (actAt Y x a) b := by
    rw [eval_two_points_eq_subst (m := 2) _ _ _ rfl, VP.subst_subst hQ1 (constantCoeff_pair_substitution ha hb)]
    unfold hAt
    congr 1
    funext q
    rcases q with ⟨i, k⟩
    fin_cases i
    · show MvPowerSeries.subst (P2 a b) (actAt Y x (pt C dd 0) k) = actAt Y x a k
      rw [actAt_pt Y ha hb]
      rfl
    · show MvPowerSeries.subst (P2 a b) (pt C dd 1 k) = b k
      rw [pair_subst_coordinate ha hb]
      rfl
  have e2 : MvPowerSeries.subst (P2 a b) (ev ![pt C dd 0, actAt Y (star x) (pt C dd 1)] Y.h) =
      hAt Y a (actAt Y (star x) b) := by
    rw [eval_two_points_eq_subst (m := 2) _ _ _ rfl, VP.subst_subst hQ2 (constantCoeff_pair_substitution ha hb)]
    unfold hAt
    congr 1
    funext q
    rcases q with ⟨i, k⟩
    fin_cases i
    · show MvPowerSeries.subst (P2 a b) (pt C dd 0 k) = a k
      rw [pair_subst_coordinate ha hb]
      rfl
    · show MvPowerSeries.subst (P2 a b) (actAt Y (star x) (pt C dd 1) k) = actAt Y (star x) b k
      rw [actAt_pt Y ha hb]
      rfl
  have hcc : MvPowerSeries.constantCoeff (ev ![actAt Y x (pt C dd 0), pt C dd 1] Y.h -
      ev ![pt C dd (0 : Fin 2), actAt Y (star x) (pt C dd (1 : Fin 2))] Y.h) = 0 := by
    rw [map_sub, eval_two_points_eq_subst (m := 2) _ _ _ rfl, eval_two_points_eq_subst (m := 2) _ _ _ rfl, VP.cc_subst hQ1 (cc_h Y),
      VP.cc_subst hQ2 (cc_h Y), sub_zero]
  rw [hx, expS_eq _ hcc, subst_exp (constantCoeff_pair_substitution ha hb) hcc, subst_sub' (constantCoeff_pair_substitution ha hb), e1, e2]

end VP

end Formalism.L2.FormalSeriesBounds
