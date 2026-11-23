import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.ChartChg
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.CalcExp

set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB

namespace GlobalTheory.FramePull

section Ev

variable {R : Type} [CommRing R] {d : ℕ}

theorem hasSubst_points {n m : ℕ} {a : Fin m → Pt R n d} (h : ∀ j i, constantCoeff (a j i) = 0) :
    HasSubst (fun p : Fin m × Fin d => a p.1 p.2) :=
  hasSubst_of_constantCoeff_zero fun p => h p.1 p.2

theorem ev_comp {n m l : ℕ} {a : Fin m → Pt R n d} {b : Fin n → Pt R l d}
    (ha : ∀ j i, constantCoeff (a j i) = 0) (hb : ∀ j i, constantCoeff (b j i) = 0) (f : PS R m d) :
    ev b (ev a f) = ev (fun j i => ev b (a j i)) f := by
  unfold ev
  rw [subst_comp_subst_apply (hasSubst_points ha) (hasSubst_points hb)]

theorem ev_point {n m : ℕ} {a : Fin m → Pt R n d} (ha : ∀ j i, constantCoeff (a j i) = 0) (j : Fin m)
    (i : Fin d) : ev a (pt R d j i) = a j i := by
  unfold ev pt
  rw [subst_X (hasSubst_points ha)]

theorem ev_plus {n m : ℕ} {a : Fin m → Pt R n d} (ha : ∀ j i, constantCoeff (a j i) = 0) (f g : PS R m d) :
    ev a (f + g) = ev a f + ev a g := subst_add (hasSubst_points ha) f g

theorem ev_minus {n m : ℕ} {a : Fin m → Pt R n d} (ha : ∀ j i, constantCoeff (a j i) = 0) (f g : PS R m d) :
    ev a (f - g) = ev a f - ev a g := subst_sub (hasSubst_points ha) f g

theorem constantCoeff_ev_eq {n m : ℕ} {a : Fin m → Pt R n d} (ha : ∀ j i, constantCoeff (a j i) = 0)
    (f : PS R m d) : constantCoeff (ev a f) = constantCoeff f := by
  have e : f = (f - C (constantCoeff f)) + C (constantCoeff f) := by ring
  have h0 : constantCoeff (ev a (f - C (constantCoeff f))) = 0 :=
    constantCoeff_subst_eq_zero (hasSubst_points ha) (fun p => ha p.1 p.2) (by simp)
  conv_lhs => rw [e, ev_plus ha, map_add, h0]
  simp [ev]

theorem map_ev_eq {k : Type} [CommRing k] (φ : R →+* k) {n m : ℕ} {a : Fin m → Pt R n d}
    (ha : ∀ j i, constantCoeff (a j i) = 0) (f : PS R m d) :
    MvPowerSeries.map φ (ev a f) = ev (fun j i => MvPowerSeries.map φ (a j i)) (MvPowerSeries.map φ f) :=
  map_subst (hasSubst_points ha) f

theorem constantCoeff_point {n : ℕ} (j : Fin n) (i : Fin d) : constantCoeff (pt R d j i) = 0 := by
  simp [pt]

theorem cz1 {n : ℕ} {x : Pt R n d} (hx : ∀ i, constantCoeff (x i) = 0) :
    ∀ j i, constantCoeff ((![x] : Fin 1 → Pt R n d) j i) = 0 := by
  intro j i; fin_cases j; exact hx i

theorem cz2 {n : ℕ} {x y : Pt R n d} (hx : ∀ i, constantCoeff (x i) = 0) (hy : ∀ i, constantCoeff (y i) = 0) :
    ∀ j i, constantCoeff ((![x, y] : Fin 2 → Pt R n d) j i) = 0 := by
  intro j i; fin_cases j
  · exact hx i
  · exact hy i

theorem cz3 {n : ℕ} {x y z : Pt R n d} (hx : ∀ i, constantCoeff (x i) = 0) (hy : ∀ i, constantCoeff (y i) = 0)
    (hz : ∀ i, constantCoeff (z i) = 0) :
    ∀ j i, constantCoeff ((![x, y, z] : Fin 3 → Pt R n d) j i) = 0 := by
  intro j i; fin_cases j
  · exact hx i
  · exact hy i
  · exact hz i

theorem germ_ev_ev_single_point_comp {n l : ℕ} {x : Pt R n d} {b : Fin n → Pt R l d} (hx : ∀ i, constantCoeff (x i) = 0)
    (hb : ∀ j i, constantCoeff (b j i) = 0) (f : PS R 1 d) :
    ev b (ev ![x] f) = ev ![fun i => ev b (x i)] f := by
  rw [ev_comp (cz1 hx) hb]
  congr 1
  funext j; fin_cases j; rfl

theorem germEv_germEv_two_points {n l : ℕ} {x y : Pt R n d} {b : Fin n → Pt R l d} (hx : ∀ i, constantCoeff (x i) = 0)
    (hy : ∀ i, constantCoeff (y i) = 0) (hb : ∀ j i, constantCoeff (b j i) = 0) (f : PS R 2 d) :
    ev b (ev ![x, y] f) = ev ![fun i => ev b (x i), fun i => ev b (y i)] f := by
  rw [ev_comp (cz2 hx hy) hb]
  congr 1
  funext j; fin_cases j <;> rfl

theorem ev_point_fun {n m : ℕ} {a : Fin m → Pt R n d} (ha : ∀ j i, constantCoeff (a j i) = 0) (j : Fin m) :
    (fun i => ev a (pt R d j i)) = a j := funext fun i => ev_point ha j i

theorem ev_comp1 {n l : ℕ} (φ : Pt R 1 d) {x : Pt R n d} {b : Fin n → Pt R l d}
    (hx : ∀ i, constantCoeff (x i) = 0) (hb : ∀ j i, constantCoeff (b j i) = 0) :
    (fun i => ev b (comp1 φ x i)) = comp1 φ (fun i => ev b (x i)) :=
  funext fun i => germ_ev_ev_single_point_comp hx hb (φ i)

theorem ev_addOf {n l : ℕ} (F : Fin d → PS R 2 d) {x y : Pt R n d} {b : Fin n → Pt R l d}
    (hx : ∀ i, constantCoeff (x i) = 0) (hy : ∀ i, constantCoeff (y i) = 0)
    (hb : ∀ j i, constantCoeff (b j i) = 0) :
    (fun i => ev b (addOf F x y i)) = addOf F (fun i => ev b (x i)) (fun i => ev b (y i)) :=
  funext fun i => germEv_germEv_two_points hx hy hb (F i)

theorem constantCoeff_comp1 {n : ℕ} {φ : Pt R 1 d} {x : Pt R n d} (hφ : ∀ i, constantCoeff (φ i) = 0)
    (hx : ∀ i, constantCoeff (x i) = 0) (i : Fin d) : constantCoeff (comp1 φ x i) = 0 := by
  rw [comp1, constantCoeff_ev_eq (cz1 hx), hφ]

theorem constantCoeff_addOf {n : ℕ} {F : Fin d → PS R 2 d} {x y : Pt R n d} (hF : ∀ i, constantCoeff (F i) = 0)
    (hx : ∀ i, constantCoeff (x i) = 0) (hy : ∀ i, constantCoeff (y i) = 0) (i : Fin d) :
    constantCoeff (addOf F x y i) = 0 := by
  rw [addOf, constantCoeff_ev_eq (cz2 hx hy), hF]

end Ev

section Integral

variable (R : Type) [CommRing R] {d : ℕ} {k : Type} [CommRing k] [Algebra ℚ k] [Algebra R k]

def ExpIntegral (f : PS k 1 d) : Prop :=
  constantCoeff f = 0 ∧ ∃ w : PS R 1 d, constantCoeff w = 1 ∧ FB.toK k w = FB.expS k f

variable {R}

theorem ExpIntegral.add {f g : PS k 1 d} (hf : ExpIntegral R f) (hg : ExpIntegral R g) :
    ExpIntegral R (f + g) := by
  obtain ⟨f0, v, v1, hv⟩ := hf
  obtain ⟨g0, w, w1, hw⟩ := hg
  refine ⟨by simp [f0, g0], v * w, by simp [v1, w1], ?_⟩
  rw [FB.toK, map_mul]
  unfold FB.expS
  rw [WickVanishing.exp_add f0 g0]
  exact congrArg₂ (· * ·) hv hw

theorem ExpIntegral.neg {f : PS k 1 d} (hf : ExpIntegral R f) : ExpIntegral R (-f) := by
  obtain ⟨f0, v, v1, hv⟩ := hf
  have n0 : constantCoeff (-f) = 0 := by simp [f0]
  refine ⟨n0, invOfUnit v 1, by simp, ?_⟩
  have h1 : FB.toK k v * FB.toK k (invOfUnit v 1) = 1 := by
    rw [FB.toK, FB.toK, ← map_mul, mul_invOfUnit v 1 (by simpa using v1), map_one]
  have h2 : FB.expS k (-f) * FB.expS k f = 1 := by
    unfold FB.expS
    rw [← WickVanishing.exp_add n0 f0, neg_add_cancel, WickVanishing.exp_zero]
  rw [hv] at h1
  calc FB.toK k (invOfUnit v 1) = (FB.expS k (-f) * FB.expS k f) * FB.toK k (invOfUnit v 1) := by
        rw [h2, _root_.one_mul]
    _ = FB.expS k (-f) := by rw [_root_.mul_assoc, h1, _root_.mul_one]

theorem expIntegral_ev {m : ℕ} {a : Fin m → Pt R 1 d} (ha : ∀ j i, constantCoeff (a j i) = 0)
    {w : PS R m d} (w1 : constantCoeff w = 1) {f : PS k m d} (f0 : constantCoeff f = 0)
    (hw : FB.toK k w = FB.expS k f) :
    ExpIntegral R (ev (fun j i => FB.toK k (a j i)) f) := by
  have ha' : ∀ j i, constantCoeff (FB.toK k (a j i)) = 0 := fun j i => by simp [FB.toK, ha]
  refine ⟨by rw [constantCoeff_ev_eq ha', f0], ev a w, by rw [constantCoeff_ev_eq ha, w1], ?_⟩
  have e1 : FB.toK k (ev a w) = ev (fun j i => FB.toK k (a j i)) (FB.toK k w) := map_ev_eq _ ha w
  rw [e1, hw]
  unfold ev FB.expS
  exact WickVanishing.subst_exp (fun p : Fin m × Fin d => FB.toK k (a p.1 p.2)) (fun p => ha' p.1 p.2) f0

end Integral

section Main

variable {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O]
  {k : Type} [CommRing k] [Algebra ℚ k] [Algebra R k] (B : FB R d O)

omit [Algebra ℚ k] in
theorem constantCoeff_actK (a : O) (i : Fin d) : constantCoeff (B.actK k a i) = 0 := by
  simp [FB.actK, B.A.const]

omit [Algebra ℚ k] in
theorem constantCoeff_FK (i : Fin d) : constantCoeff (B.FK k i) = 0 := by
  simp [FB.FK, FGLaw.mapF, B.G.const]

omit [Algebra ℚ k] in
theorem actK_mul (a b : O) : B.actK k (a * b) = comp1 (B.actK k a) (B.actK k b) := by
  funext i
  simp only [FB.actK, B.A.mul_act, comp1]
  rw [map_ev_eq _ (cz1 (B.A.const b))]
  congr 1
  funext j; fin_cases j; rfl

omit [Algebra ℚ k] in
theorem actK_add (a b : O) : B.actK k (a + b) = addOf (B.FK k) (B.actK k a) (B.actK k b) := by
  funext i
  simp only [FB.actK, B.A.add_act, addOf]
  rw [map_ev_eq _ (cz2 (B.A.const a) (B.A.const b))]
  congr 1
  funext j; fin_cases j <;> rfl

omit [Algebra ℚ k] in
theorem actK_one : B.actK k 1 = pt k d 0 := by
  funext i
  simp [FB.actK, B.A.one_act, pt]

variable {B} {h : PS k 2 d}

theorem expIntegral_ad (hh : B.IsCanonGauge k h) (a b c : O) :
    ExpIntegral R (ev ![B.actK k (a * b), B.actK k c] h - ev ![B.actK k b, B.actK k (star a * c)] h) := by
  have p0 : ∀ {n : ℕ} (j : Fin n) (i : Fin d), constantCoeff (pt k d j i) = 0 := constantCoeff_point
  have c0 : ∀ (e : O) (j : Fin 2) (i : Fin d), constantCoeff (comp1 (B.actK k e) (pt k d j) i) = 0 :=
    fun e j => constantCoeff_comp1 (constantCoeff_actK B e) (p0 j)
  have w1 : constantCoeff (B.ad a) = 1 := by
    rw [← constantCoeff_ev_eq (cz2 (x := (0 : Pt R 1 d)) (fun _ => by simp) (constantCoeff_point 0)),
      B.adjoint_zero_fst, map_one]
  have key := expIntegral_ev (cz2 (B.A.const b) (B.A.const c)) w1 (by
    rw [map_sub, constantCoeff_ev_eq (cz2 (c0 a 0) (p0 1)), constantCoeff_ev_eq (cz2 (p0 0) (c0 _ 1)),
      sub_self]) (hh.ad a)
  have e : (fun j i => FB.toK k ((![B.A.act b, B.A.act c] : Fin 2 → Pt R 1 d) j i)) =
      ![B.actK k b, B.actK k c] := by
    funext j; fin_cases j <;> rfl
  have hb := cz2 (constantCoeff_actK (k := k) B b) (constantCoeff_actK (k := k) B c)
  rw [e, ev_minus hb, germEv_germEv_two_points (c0 a 0) (p0 1) hb, germEv_germEv_two_points (p0 0) (c0 _ 1) hb, ev_comp1 _ (p0 0) hb,
    ev_comp1 _ (p0 1) hb, ev_point_fun hb, ev_point_fun hb] at key
  rw [actK_mul, actK_mul]
  exact key

theorem powerSeriesExpIntegral_canonGauge_additive_second (hh : B.IsCanonGauge k h) (b c c' : O) :
    ExpIntegral R (ev ![B.actK k b, B.actK k c] h + ev ![B.actK k b, B.actK k c'] h -
      ev ![B.actK k b, B.actK k (c + c')] h) := by
  have p0 : ∀ {n : ℕ} (j : Fin n) (i : Fin d), constantCoeff (pt k d j i) = 0 := constantCoeff_point
  have c0 : ∀ (i : Fin d), constantCoeff (addOf (B.FK k) (pt k (n := 3) d 1) (pt k d 2) i) = 0 :=
    constantCoeff_addOf (constantCoeff_FK B) (p0 1) (p0 2)
  have h0 : constantCoeff h = 0 := by
    rw [← constantCoeff_ev_eq (cz2 (x := (0 : Pt k 1 d)) (fun _ => by simp) (constantCoeff_point 0)),
      hh.ax0, map_zero]
  have w1 : constantCoeff B.ph2 = 1 := by
    rw [← constantCoeff_ev_eq (cz3 (x := (0 : Pt R 2 d)) (fun _ => by simp) (constantCoeff_point 0)
      (constantCoeff_point 1)), B.cocycleRight_zero_fst, map_one]
  have key := expIntegral_ev (cz3 (B.A.const b) (B.A.const c) (B.A.const c')) w1 (by
    rw [map_sub, map_add, constantCoeff_ev_eq (cz2 (p0 0) (p0 1)), constantCoeff_ev_eq (cz2 (p0 0) (p0 2)),
      constantCoeff_ev_eq (cz2 (p0 0) c0), h0]
    simp) hh.ph2
  have e : (fun j i => FB.toK k ((![B.A.act b, B.A.act c, B.A.act c'] : Fin 3 → Pt R 1 d) j i)) =
      ![B.actK k b, B.actK k c, B.actK k c'] := by
    funext j; fin_cases j <;> rfl
  have hb := cz3 (constantCoeff_actK (k := k) B b) (constantCoeff_actK (k := k) B c)
    (constantCoeff_actK (k := k) B c')
  rw [e, ev_minus hb, ev_plus hb, germEv_germEv_two_points (p0 0) (p0 1) hb, germEv_germEv_two_points (p0 0) (p0 2) hb, germEv_germEv_two_points (p0 0) c0 hb,
    ev_addOf _ (p0 1) (p0 2) hb, ev_point_fun hb, ev_point_fun hb, ev_point_fun hb] at key
  rw [actK_add]
  exact key

theorem expIntegral_nsmul (hh : B.IsCanonGauge k h) (b c : O) (j : ℕ) :
    ExpIntegral R ((j : k) • ev ![B.actK k b, B.actK k c] h - ev ![B.actK k b, B.actK k ((j : O) * c)] h) := by
  induction j with
  | zero =>
    have := (powerSeriesExpIntegral_canonGauge_additive_second hh b 0 0).neg
    simpa using this
  | succ j ih =>
    have := ih.add (powerSeriesExpIntegral_canonGauge_additive_second hh b ((j : O) * c) c)
    convert this using 1
    rw [Nat.cast_succ, Nat.cast_succ, add_smul, one_smul, add_mul, _root_.one_mul]
    ring

omit [Algebra ℚ k] in
theorem ev_actK_hL (w0 a : O) :
    ev (n := 1) ![B.actK k a] (B.hL k h w0) = ev ![B.actK k a, B.actK k (w0 * a)] h := by
  have hb := cz1 (constantCoeff_actK (k := k) B a)
  rw [FB.hL, germEv_germEv_two_points (constantCoeff_point 0) (constantCoeff_comp1 (constantCoeff_actK B w0)
    (constantCoeff_point 0)) hb, ev_comp1 _ (constantCoeff_point 0) hb, ev_point_fun hb, actK_mul]
  rfl

omit [Algebra ℚ k] in
theorem hL_eq (w0 : O) : B.hL k h w0 = ev ![B.actK k 1, B.actK k w0] h := by
  rw [FB.hL, ← actK_one B, ← actK_mul, _root_.mul_one]

end Main

theorem exists_integral_frame_pullback :
    ∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (k : Type) [CommRing k]
      [Algebra ℚ k] [Algebra R k] (B : FB R d O) (h : PS k 2 d), B.IsCanonGauge k h →
      ∀ (w0 a : O) (N : ℕ), a * star a = (N : O) → ∃ w : PS R 1 d, constantCoeff w = 1 ∧
        FB.toK k w = FB.expS k (ev (n := 1) ![B.actK k a] (B.hL k h w0) - (N : k) • B.hL k h w0) := by
  intro R _ d O _ _ k _ _ _ B h hh w0 a N hN
  have h1 := expIntegral_ad hh a 1 (w0 * a)
  have h2 := (expIntegral_nsmul hh 1 w0 N).neg
  have e : star a * (w0 * a) = (N : O) * w0 := by rw [← hN]; ring
  rw [e, _root_.mul_one] at h1
  have h3 := (h1.add h2).2
  rw [ev_actK_hL, hL_eq]
  convert h3 using 5
  ring

end GlobalTheory.FramePull
