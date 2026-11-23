import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwoChartAtlas.TwoChartSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.ChartChg
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.GaugeTrans
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.CalcExp

set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing GlobalTheory.JetSer

namespace GlobalTheory.JetSer.IntTrans

section Map

variable {R k : Type} [CommRing R] [CommRing k] (f : R →+* k) {d : ℕ}

def mP {n : ℕ} (a : Pt R n d) : Pt k n d := fun i => MvPowerSeries.map f (a i)

theorem map_ev {m n : ℕ} (a : Fin m → Pt R n d) (ha : ∀ j, GP (a j)) (g : PS R m d) :
    MvPowerSeries.map f (ev a g) = ev (fun j => mP f (a j)) (MvPowerSeries.map f g) := by
  unfold ev
  rw [MvPowerSeries.map_subst (gt_hasSubst a ha)]
  rfl

theorem map_ev1 {n : ℕ} {a : Pt R n d} (ha : GP a) (g : PS R 1 d) :
    MvPowerSeries.map f (ev ![a] g) = ev ![mP f a] (MvPowerSeries.map f g) := by
  rw [map_ev f _ (single_point_zero_constant ha)]
  congr 1
  funext j; fin_cases j; rfl

theorem map_ev2 {n : ℕ} {a b : Pt R n d} (ha : GP a) (hb : GP b) (g : PS R 2 d) :
    MvPowerSeries.map f (ev ![a, b] g) = ev ![mP f a, mP f b] (MvPowerSeries.map f g) := by
  rw [map_ev f _ (pair_points_zero_constant ha hb)]
  congr 1
  funext j; fin_cases j <;> rfl

theorem map_ev3 {n : ℕ} {a b c : Pt R n d} (ha : GP a) (hb : GP b) (hc : GP c) (g : PS R 3 d) :
    MvPowerSeries.map f (ev ![a, b, c] g) = ev ![mP f a, mP f b, mP f c] (MvPowerSeries.map f g) := by
  rw [map_ev f _ (triple_points_zero_constant ha hb hc)]
  congr 1
  funext j; fin_cases j <;> rfl

theorem mapPoint_pt {n : ℕ} (j : Fin n) : mP f (pt R d j) = pt k d j := by
  funext i; simp [mP, pt]

theorem mapPoint_zero {n : ℕ} : mP f (0 : Pt R n d) = 0 := by
  funext i; simp [mP]

theorem mapPoint_comp1 {n : ℕ} (φ : Pt R 1 d) {a : Pt R n d} (ha : GP a) :
    mP f (comp1 φ a) = comp1 (mP f φ) (mP f a) := funext fun i => map_ev1 f ha (φ i)

theorem mapPoint_addOf {n : ℕ} (F : Pt R 2 d) {a b : Pt R n d} (ha : GP a) (hb : GP b) :
    mP f (addOf F a b) = addOf (mP f F) (mP f a) (mP f b) := funext fun i => map_ev2 f ha hb (F i)

theorem constantCoeff_map_eq_zero₂ {n : ℕ} {a : Pt R n d} (ha : GP a) : GP (mP f a) := fun i => by
  simp only [mP, constantCoeff_map, ha i, map_zero]

theorem related_map {O : Type} [CommRing O] [StarRing O] {B B' : FB R d O} {φ φi : Pt R 1 d} {ε : PS R 2 d}
    (h : Related B B' φ φi ε) {C C' : FB k d O}
    (hF : C.G.F = mP f B.G.F) (hA : ∀ a, C.A.act a = mP f (B.A.act a))
    (h1 : C.ph1 = MvPowerSeries.map f B.ph1) (h2 : C.ph2 = MvPowerSeries.map f B.ph2)
    (hs : C.sy = MvPowerSeries.map f B.sy) (hd : ∀ a, C.ad a = MvPowerSeries.map f (B.ad a))
    (hF' : C'.G.F = mP f B'.G.F) (hA' : ∀ a, C'.A.act a = mP f (B'.A.act a))
    (h1' : C'.ph1 = MvPowerSeries.map f B'.ph1) (h2' : C'.ph2 = MvPowerSeries.map f B'.ph2)
    (hs' : C'.sy = MvPowerSeries.map f B'.sy) (hd' : ∀ a, C'.ad a = MvPowerSeries.map f (B'.ad a)) :
    Related C C' (mP f φ) (mP f φi) (MvPowerSeries.map f ε) := by
  have hφ : GP φ := h.inv.1
  have hφi : GP φi := h.inv.2.1
  have hp : ∀ {n : ℕ} (j : Fin n), GP (pt R (n := n) d j) := fun j => gp_pt j
  have hc : ∀ {n : ℕ} (j : Fin n), GP (comp1 φ (pt R (n := n) d j)) := fun j => gp_comp1 φ _ hφ (hp j)
  have mc : ∀ {n : ℕ} (ψ : Pt R 1 d) (j : Fin n),
      mP f (comp1 ψ (pt R (n := n) d j)) = comp1 (mP f ψ) (pt k d j) := fun ψ j => by
    rw [mapPoint_comp1 f ψ (hp j), mapPoint_pt]
  have hBa : ∀ a, GP (B.A.act a) := B.A.const
  have hBa' : ∀ a, GP (B'.A.act a) := B'.A.const
  refine ⟨⟨constantCoeff_map_eq_zero₂ f hφ, constantCoeff_map_eq_zero₂ f hφi, ?_, ?_⟩, ?_, ?_, fun i => ?_, fun a => ?_, ?_, ?_, ?_, fun a => ?_⟩
  · rw [← mapPoint_comp1 f φ hφi, h.inv.2.2.1, mapPoint_pt]
  · rw [← mapPoint_comp1 f φi hφ, h.inv.2.2.2, mapPoint_pt]
  · have := congrArg (MvPowerSeries.map f) h.ax0
    rwa [map_ev2 f gp_zero₂ (hp 0), mapPoint_zero, mapPoint_pt, map_one] at this
  · have := congrArg (MvPowerSeries.map f) h.ax1
    rwa [map_ev2 f (hp 0) gp_zero₂, mapPoint_zero, mapPoint_pt, map_one] at this
  · have := congrArg (MvPowerSeries.map f) (h.law i)
    unfold transF at this ⊢
    rw [map_ev1 f (gp_addOf _ B.G.const _ _ (hc 0) (hc 1)), mapPoint_addOf f _ (hc 0) (hc 1), mc, mc] at this
    rw [hF', hF]
    exact this
  · rw [hA', hA, h.act a, mapPoint_comp1 f φi (gp_comp1 _ _ (hBa a) hφ), mapPoint_comp1 f _ hφ]
  · have := congrArg (MvPowerSeries.map f) h.ph1
    rw [map_mul, map_mul, map_mul, map_ev2 f (gp_addOf _ B'.G.const _ _ (hp 0) (hp 1)) (hp 2),
      map_ev3 f (hc 0) (hc 1) (hc 2), map_ev2 f (hp 0) (hp 2), map_ev2 f (hp 1) (hp 2),
      mapPoint_addOf f _ (hp 0) (hp 1), mc, mc, mc, mapPoint_pt, mapPoint_pt, mapPoint_pt] at this
    rw [hF', h1', h1]
    exact this
  · have := congrArg (MvPowerSeries.map f) h.ph2
    rw [map_mul, map_mul, map_mul, map_ev2 f (hp 0) (gp_addOf _ B'.G.const _ _ (hp 1) (hp 2)),
      map_ev3 f (hc 0) (hc 1) (hc 2), map_ev2 f (hp 0) (hp 1), map_ev2 f (hp 0) (hp 2),
      mapPoint_addOf f _ (hp 1) (hp 2), mc, mc, mc, mapPoint_pt, mapPoint_pt, mapPoint_pt] at this
    rw [hF', h2', h2]
    exact this
  · have := congrArg (MvPowerSeries.map f) h.sy
    rw [map_mul, map_mul, map_ev2 f (hc 0) (hc 1), map_ev2 f (hp 1) (hp 0), mc, mc, mapPoint_pt, mapPoint_pt] at this
    rw [hs', hs]
    exact this
  · have := congrArg (MvPowerSeries.map f) (h.ad a)
    rw [map_mul, map_mul, map_ev2 f (hc 0) (hc 1),
      map_ev2 f (hp 0) (gp_comp1 _ _ (hBa' _) (hp 1)),
      map_ev2 f (gp_comp1 _ _ (hBa' _) (hp 0)) (hp 1), mc, mc, mc, mc, mapPoint_pt, mapPoint_pt] at this
    rw [hd', hd, hA', hA']
    exact this

end Map

section Core

variable {k : Type} [CommRing k] [Algebra ℚ k] {d : ℕ}

theorem expS_zero {n : ℕ} : FB.expS k (0 : PS k n d) = 1 := exp_zero

theorem solve_exp {n : ℕ} {x y a c : PS k n d} (ha : constantCoeff a = 0) (hc : constantCoeff c = 0)
    (h : x * FB.expS k c = y * FB.expS k a) : x = y * FB.expS k (a - c) := by
  have hn : constantCoeff (-c) = 0 := by rw [map_neg, hc, neg_zero]
  rw [sub_eq_add_neg, gt_expS_add _ _ ha hn, ← _root_.mul_assoc, ← h, _root_.mul_assoc, ← gt_expS_add _ _ hc hn,
    add_neg_cancel, expS_zero, _root_.mul_one]

theorem expS_nsmul {n : ℕ} {a : PS k n d} (ha : constantCoeff a = 0) (m : ℕ) :
    FB.expS k ((m : k) • a) = FB.expS k a ^ m := by
  rw [Nat.cast_smul_eq_nsmul]
  induction m with
  | zero => rw [zero_nsmul, expS_zero, pow_zero]
  | succ m ih => rw [succ_nsmul, gt_expS_add _ _ (by rw [map_nsmul, ha, nsmul_zero]) ha, ih, pow_succ]

theorem unit_right (G : FGLaw k d) (i : Fin d) :
    ev (n := 1) ![pt k (n := 1) d 0, 0] (G.F i) = (X ((0 : Fin 1), i) : PS k 1 d) := by
  have hV : ∀ j, GP (![pt k (n := 1) d 0, 0] j) := pair_points_zero_constant (gp_pt 0) gp_zero₂
  rw [← G.comm i, gt_ev_ev' _ _ hV (pair_points_zero_constant (gp_pt 1) (gp_pt 0)), eval_pair_points, evP_pt _ hV, evP_pt _ hV]
  exact G.unit i

theorem core (hN : NabTransSt) {O : Type} [CommRing O] [StarRing O] {B B' : FB k d O} {φ φi : Pt k 1 d}
    {ε : PS k 2 d} (r : Related B B' φ φi ε) (h : PS k 2 d) (hh : B.IsCanonGauge k h) :
    ∃ h' : PS k 2 d, B'.IsCanonGauge k h' ∧ ∀ (w0 : O) (m : ℕ) (f f' : PS k 1 d),
      f' * ev (n := 1) ![pt k (n := 1) d 0, comp1 (B'.A.act w0) (pt k (n := 1) d 0)] ε ^ m =
        ev (n := 1) ![φ] f →
      ∀ (Λ : Type) [Fintype Λ] (u : Λ → Fin d → k) (P : MvPolynomial Λ k),
        B'.nabVal k h' w0 m f' u P = B.nabVal k h w0 m f (fun l => (dLin φ).mulVec (u l)) P := by
  have hp : ∀ {n : ℕ} (j : Fin n), GP (pt k (n := n) d j) := fun j => gp_pt j
  have hz : ∀ {n : ℕ}, GP (0 : Pt k n d) := gp_zero₂
  have hε : constantCoeff ε = 1 := by
    have := congrArg constantCoeff r.ax0
    rwa [gt_const_ev_eq _ (pair_points_zero_constant hz (hp 0)), map_one] at this
  obtain ⟨lam, hl, he⟩ : ∃ lam : PS k 2 d, constantCoeff lam = 0 ∧ FB.expS k lam = ε :=
    ⟨_, constantCoeff_logS hε, exp_log hε⟩
  subst he
  have E : ∀ {n : ℕ} {a b : Pt k n d}, GP a → GP b →
      ev ![a, b] (FB.expS k lam) = FB.expS k (ev ![a, b] lam) := fun ha hb => gt_ev_expS _ (pair_points_zero_constant ha hb) _ hl
  have Z : ∀ {n : ℕ} {a b : Pt k n d}, GP a → GP b →
      constantCoeff (ev ![a, b] lam) = 0 := fun ha hb => gt_const_ev _ (pair_points_zero_constant ha hb) _ hl
  have l0 : ev (n := 1) ![0, pt k (n := 1) d 0] lam = 0 :=
    eq_zero_of_exp_eq_one (Z hz (hp 0)) ((E hz (hp 0)).symm.trans r.ax0)
  have l1 : ev (n := 1) ![pt k (n := 1) d 0, 0] lam = 0 :=
    eq_zero_of_exp_eq_one (Z (hp 0) hz) ((E (hp 0) hz).symm.trans r.ax1)
  have hBa' : ∀ a, GP (B'.A.act a) := B'.A.const
  refine ⟨_, gauge_transformation k d O B B' φ φi lam r.inv l0 l1 r.law r.act ?_ ?_ ?_ (fun a => ?_) h hh, ?_⟩
  · have g := gp_addOf _ B'.G.const _ _ (hp (n := 3) 0) (hp 1)
    have := r.ph1
    rw [E g (hp 2), E (hp 0) (hp 2), E (hp 1) (hp 2), ← gt_expS_add _ _ (Z (hp 0) (hp 2)) (Z (hp 1) (hp 2))] at this
    exact solve_exp (by rw [map_add, Z (hp 0) (hp 2), Z (hp 1) (hp 2), add_zero]) (Z g (hp 2)) this
  · have g := gp_addOf _ B'.G.const _ _ (hp (n := 3) 1) (hp 2)
    have := r.ph2
    rw [E (hp 0) g, E (hp 0) (hp 1), E (hp 0) (hp 2), ← gt_expS_add _ _ (Z (hp 0) (hp 1)) (Z (hp 0) (hp 2))] at this
    exact solve_exp (by rw [map_add, Z (hp 0) (hp 1), Z (hp 0) (hp 2), add_zero]) (Z (hp 0) g) this
  · have := r.sy
    rw [E (hp 1) (hp 0)] at this
    exact solve_exp (Z (hp 1) (hp 0)) hl this
  · have g0 := gp_comp1 _ _ (hBa' a) (hp (n := 2) 0)
    have g1 := gp_comp1 _ _ (hBa' (star a)) (hp (n := 2) 1)
    have := r.ad a
    rw [E (hp 0) g1, E g0 (hp 1)] at this
    exact solve_exp (Z g0 (hp 1)) (Z (hp 0) g1) this
  · intro w0 m f f' hf Λ _ u P
    have ak : B'.actK k w0 = B'.A.act w0 := funext fun i => gt_map_id _
    have g := gp_comp1 _ _ (hBa' w0) (hp (n := 1) 0)
    rw [← hN k d O B B' φ φi lam r.inv l0 l1 (unit_right B.G) r.law r.act h hh.ax0 w0 m f Λ u P, ak]
    congr 1
    rw [E (hp 0) g, ← expS_nsmul (Z (hp 0) g)] at hf
    have := solve_exp (x := f') (y := ev ![φ] f) (a := 0)
      (c := (m : k) • ev (n := 1) ![pt k (n := 1) d 0, comp1 (B'.A.act w0) (pt k (n := 1) d 0)] lam) (map_zero _)
      (by rw [Nat.cast_smul_eq_nsmul, map_nsmul, Z (hp 0) g, nsmul_zero])
      (by rw [expS_zero, _root_.mul_one]; exact hf)
    rwa [zero_sub] at this

end Core

section BC

variable {R k : Type} [CommRing R] [CommRing k] [Algebra ℚ k] [Algebra R k] {d : ℕ}
  {O : Type} [CommRing O] [StarRing O] {B : FB R d O} {C : FB k d O}

theorem FK_eq (hF : C.G.F = mP (algebraMap R k) B.G.F) : C.FK k = B.FK k := by
  funext i
  exact (gt_map_id _).trans (congrFun hF i)

theorem actK_eq (hA : ∀ a, C.A.act a = mP (algebraMap R k) (B.A.act a)) (a : O) : C.actK k a = B.actK k a := by
  funext i
  exact (gt_map_id _).trans (congrFun (hA a) i)

theorem canon_iff (hF : C.G.F = mP (algebraMap R k) B.G.F) (hA : ∀ a, C.A.act a = mP (algebraMap R k) (B.A.act a))
    (h1 : C.ph1 = MvPowerSeries.map (algebraMap R k) B.ph1) (h2 : C.ph2 = MvPowerSeries.map (algebraMap R k) B.ph2)
    (hs : C.sy = MvPowerSeries.map (algebraMap R k) B.sy)
    (hd : ∀ a, C.ad a = MvPowerSeries.map (algebraMap R k) (B.ad a)) (h : PS k 2 d) :
    C.IsCanonGauge k h ↔ B.IsCanonGauge k h := by
  have e1 : FB.toK k C.ph1 = FB.toK k B.ph1 := (gt_map_id _).trans h1
  have e2 : FB.toK k C.ph2 = FB.toK k B.ph2 := (gt_map_id _).trans h2
  have e3 : FB.toK k C.sy = FB.toK k B.sy := (gt_map_id _).trans hs
  have e4 : ∀ a, FB.toK k (C.ad a) = FB.toK k (B.ad a) := fun a => (gt_map_id _).trans (hd a)
  constructor
  · intro g
    refine ⟨g.ax0, g.ax1, ?_, ?_, ?_, fun a => ?_⟩
    · rw [← e1, ← FK_eq hF]; exact g.ph1
    · rw [← e2, ← FK_eq hF]; exact g.ph2
    · rw [← e3]; exact g.sy
    · rw [← e4, ← actK_eq hA, ← actK_eq hA]; exact g.ad a
  · intro g
    refine ⟨g.ax0, g.ax1, ?_, ?_, ?_, fun a => ?_⟩
    · rw [e1, FK_eq hF]; exact g.ph1
    · rw [e2, FK_eq hF]; exact g.ph2
    · rw [e3]; exact g.sy
    · rw [e4, actK_eq hA, actK_eq hA]; exact g.ad a

theorem nabVal_eq (hF : C.G.F = mP (algebraMap R k) B.G.F) (hA : ∀ a, C.A.act a = mP (algebraMap R k) (B.A.act a))
    (h : PS k 2 d) (w0 : O) (m : ℕ) (f : PS k 1 d) {ι : Type} [Fintype ι]
    (u : ι → Fin d → k) (P : MvPolynomial ι k) : C.nabVal k h w0 m f u P = B.nabVal k h w0 m f u P := by
  unfold FB.nabVal FB.hL
  rw [FK_eq hF, actK_eq hA]

end BC

theorem intTrans (hN : NabTransSt)
    (hBC : ∀ (R k : Type) [CommRing R] [CommRing k] (f : R →+* k) (d : ℕ) (O : Type) [CommRing O] [StarRing O]
      (B : FB R d O), ∃ B' : FB k d O, (∀ i, B'.G.F i = MvPowerSeries.map f (B.G.F i)) ∧
        (∀ a i, B'.A.act a i = MvPowerSeries.map f (B.A.act a i)) ∧ B'.ph1 = MvPowerSeries.map f B.ph1 ∧
        B'.ph2 = MvPowerSeries.map f B.ph2 ∧ B'.sy = MvPowerSeries.map f B.sy ∧
        ∀ a, B'.ad a = MvPowerSeries.map f (B.ad a)) : IntTransSt := by
  intro R _ d O _ _ B B' φ φi ε r k _ _ _ h hh
  obtain ⟨C, hF, hA, h1, h2, hs, hd⟩ := hBC R k (algebraMap R k) d O B
  obtain ⟨C', hF', hA', h1', h2', hs', hd'⟩ := hBC R k (algebraMap R k) d O B'
  have hF : C.G.F = mP (algebraMap R k) B.G.F := funext hF
  have hF' : C'.G.F = mP (algebraMap R k) B'.G.F := funext hF'
  have hA : ∀ a, C.A.act a = mP (algebraMap R k) (B.A.act a) := fun a => funext (hA a)
  have hA' : ∀ a, C'.A.act a = mP (algebraMap R k) (B'.A.act a) := fun a => funext (hA' a)
  have r' := related_map (algebraMap R k) r hF hA h1 h2 hs hd hF' hA' h1' h2' hs' hd'
  obtain ⟨h', hc, hv⟩ := core hN r' h ((canon_iff hF hA h1 h2 hs hd h).2 hh)
  refine ⟨h', (canon_iff hF' hA' h1' h2' hs' hd' h').1 hc, fun w0 m f f' hf Λ _ u P => ?_⟩
  have hd : dLin (mP (algebraMap R k) φ) = (dLin φ).map (algebraMap R k) := by
    ext i j
    simp [dLin, mP]
  rw [← nabVal_eq hF' hA', ← nabVal_eq hF hA, ← hd]
  refine hv w0 m f f' ?_ Λ u P
  rw [FB.toK, map_ev2 _ (gp_pt 0) (gp_comp1 _ _ (B'.A.const w0) (gp_pt 0)),
    mapPoint_comp1 _ _ (gp_pt 0), mapPoint_pt, ← hA'] at hf
  exact hf

end GlobalTheory.JetSer.IntTrans
