import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.ChartChg
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.WickOperatorVanishing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.GEWick
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.GaugeTrans
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.CalcExp

set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing

namespace GlobalTheory.ActionGauge

section Basic

variable {k : Type} [CommRing k] {d : ℕ}

def evAdd {m n : ℕ} (a : Fin m → Pt k n d) (ha : ∀ j, GP (a j)) : PS k m d →+ PS k n d :=
  AddMonoidHom.mk' (ev a) (gt_ev_add a ha)

theorem ev_ratSmul [Algebra ℚ k] {m n : ℕ} (a : Fin m → Pt k n d) (ha : ∀ j, GP (a j)) (q : ℚ)
    (f : PS k m d) : ev a (q • f) = q • ev a f :=
  map_rat_smul (evAdd a ha) q f

theorem ev_pt_two (f : PS k 2 d) : ev ![pt k (n := 2) d 0, pt k (n := 2) d 1] f = f := by
  change MvPowerSeries.subst
    (fun p : Fin 2 × Fin d => (![pt k (n := 2) d 0, pt k (n := 2) d 1] p.1) p.2) f = f
  have e : (fun p : Fin 2 × Fin d => (![pt k (n := 2) d 0, pt k (n := 2) d 1] p.1) p.2) = X := by
    funext p
    obtain ⟨j, i⟩ := p
    fin_cases j <;> rfl
  rw [e, MvPowerSeries.subst_self]
  rfl

theorem ev_ev_two {m n : ℕ} (V : Fin m → Pt k n d) (hV : ∀ j, GP (V j)) (a b : Pt k m d)
    (ha : GP a) (hb : GP b) (f : PS k 2 d) :
    ev V (ev ![a, b] f) = ev ![evP V a, evP V b] f := by
  rw [gt_ev_ev' V _ hV (pair_points_zero_constant ha hb), eval_pair_points]

theorem ev_left {n : ℕ} (φ : Pt k 1 d) (hφ : GP φ) (a b : Pt k n d) (ha : GP a) (hb : GP b)
    (g : PS k 2 d) :
    ev ![a, b] (ev ![comp1 φ (pt k (n := 2) d 0), pt k (n := 2) d 1] g) = ev ![comp1 φ a, b] g := by
  have hV := pair_points_zero_constant ha hb
  rw [ev_ev_two _ hV _ _ (gp_comp1 _ _ hφ (gp_pt 0)) (gp_pt 1),
    evP_comp1 _ hV _ _ (gp_pt 0), evP_pt _ hV, evP_pt _ hV]
  rfl

theorem ev_right {n : ℕ} (φ : Pt k 1 d) (hφ : GP φ) (a b : Pt k n d) (ha : GP a) (hb : GP b)
    (g : PS k 2 d) :
    ev ![a, b] (ev ![pt k (n := 2) d 0, comp1 φ (pt k (n := 2) d 1)] g) = ev ![a, comp1 φ b] g := by
  have hV := pair_points_zero_constant ha hb
  rw [ev_ev_two _ hV _ _ (gp_pt 0) (gp_comp1 _ _ hφ (gp_pt 1)),
    evP_comp1 _ hV _ _ (gp_pt 1), evP_pt _ hV, evP_pt _ hV]
  rfl

end Basic

section Act

variable {k : Type} [CommRing k] {d : ℕ} {O : Type} [CommRing O] {G : FGLaw k d} (A : OAct O G)

theorem act_addOf (c : O) {n : ℕ} (x y : Pt k n d) (hx : GP x) (hy : GP y) :
    comp1 (A.act c) (addOf G.F x y) = addOf G.F (comp1 (A.act c) x) (comp1 (A.act c) y) := by
  have hV := pair_points_zero_constant hx hy
  have hc : GP (A.act c) := A.const c
  have h := congrArg (evP ![x, y]) (A.hom c)
  rw [evP_comp1 _ hV _ _ (gp_addOf _ G.const _ _ (gp_pt 0) (gp_pt 1)),
    evP_addOf _ hV _ _ _ (gp_pt 0) (gp_pt 1),
    evP_addOf _ hV _ _ _ (gp_comp1 _ _ hc (gp_pt 0)) (gp_comp1 _ _ hc (gp_pt 1)),
    evP_comp1 _ hV _ _ (gp_pt 0), evP_comp1 _ hV _ _ (gp_pt 1),
    evP_pt _ hV, evP_pt _ hV] at h
  exact h

theorem add_act_apply (a b : O) {n : ℕ} (x : Pt k n d) (hx : GP x) :
    comp1 (A.act (a + b)) x = addOf G.F (comp1 (A.act a) x) (comp1 (A.act b) x) := by
  rw [A.add_act]
  exact evP_addOf ![x] (single_point_zero_constant hx) G.F _ _ (A.const a) (A.const b)

theorem mul_act_apply (a b : O) {n : ℕ} (x : Pt k n d) (hx : GP x) :
    comp1 (A.act (a * b)) x = comp1 (A.act a) (comp1 (A.act b) x) := by
  rw [A.mul_act]
  exact gt_comp1_comp1 _ _ (A.const b) x hx

theorem one_act_apply {n : ℕ} (x : Pt k n d) (hx : GP x) : comp1 (A.act 1) x = x := by
  rw [A.one_act]
  exact gt_comp1_pt x hx

end Act

section Biadd

variable {k : Type} [CommRing k] [Algebra ℚ k] {d : ℕ}

def biadd (G : FGLaw k d) : Submodule ℚ (PS k 2 d) where
  carrier := {g | (∀ (n : ℕ) (b : Pt k n d), GP b → ev ![0, b] g = 0) ∧
    (∀ (n : ℕ) (a : Pt k n d), GP a → ev ![a, 0] g = 0) ∧
    (∀ (n : ℕ) (a a' b : Pt k n d), GP a → GP a' → GP b →
      ev ![addOf G.F a a', b] g = ev ![a, b] g + ev ![a', b] g) ∧
    (∀ (n : ℕ) (a b b' : Pt k n d), GP a → GP b → GP b' →
      ev ![a, addOf G.F b b'] g = ev ![a, b] g + ev ![a, b'] g)}
  zero_mem' := by
    refine ⟨fun n b hb => ?_, fun n a ha => ?_, fun n a a' b ha ha' hb => ?_,
      fun n a b b' ha hb hb' => ?_⟩
    · exact gt_ev_zero _ (pair_points_zero_constant gp_zero₂ hb)
    · exact gt_ev_zero _ (pair_points_zero_constant ha gp_zero₂)
    · rw [gt_ev_zero _ (pair_points_zero_constant (gp_addOf _ G.const _ _ ha ha') hb), gt_ev_zero _ (pair_points_zero_constant ha hb),
        gt_ev_zero _ (pair_points_zero_constant ha' hb), add_zero]
    · rw [gt_ev_zero _ (pair_points_zero_constant ha (gp_addOf _ G.const _ _ hb hb')), gt_ev_zero _ (pair_points_zero_constant ha hb),
        gt_ev_zero _ (pair_points_zero_constant ha hb'), add_zero]
  add_mem' := by
    rintro f g ⟨f1, f2, f3, f4⟩ ⟨g1, g2, g3, g4⟩
    refine ⟨fun n b hb => ?_, fun n a ha => ?_, fun n a a' b ha ha' hb => ?_,
      fun n a b b' ha hb hb' => ?_⟩
    · rw [gt_ev_add _ (pair_points_zero_constant gp_zero₂ hb), f1 n b hb, g1 n b hb, add_zero]
    · rw [gt_ev_add _ (pair_points_zero_constant ha gp_zero₂), f2 n a ha, g2 n a ha, add_zero]
    · rw [gt_ev_add _ (pair_points_zero_constant (gp_addOf _ G.const _ _ ha ha') hb), gt_ev_add _ (pair_points_zero_constant ha hb),
        gt_ev_add _ (pair_points_zero_constant ha' hb), f3 n a a' b ha ha' hb, g3 n a a' b ha ha' hb]
      ring
    · rw [gt_ev_add _ (pair_points_zero_constant ha (gp_addOf _ G.const _ _ hb hb')), gt_ev_add _ (pair_points_zero_constant ha hb),
        gt_ev_add _ (pair_points_zero_constant ha hb'), f4 n a b b' ha hb hb', g4 n a b b' ha hb hb']
      ring
  smul_mem' := by
    rintro q f ⟨f1, f2, f3, f4⟩
    refine ⟨fun n b hb => ?_, fun n a ha => ?_, fun n a a' b ha ha' hb => ?_,
      fun n a b b' ha hb hb' => ?_⟩
    · rw [ev_ratSmul _ (pair_points_zero_constant gp_zero₂ hb), f1 n b hb, smul_zero]
    · rw [ev_ratSmul _ (pair_points_zero_constant ha gp_zero₂), f2 n a ha, smul_zero]
    · rw [ev_ratSmul _ (pair_points_zero_constant (gp_addOf _ G.const _ _ ha ha') hb), ev_ratSmul _ (pair_points_zero_constant ha hb),
        ev_ratSmul _ (pair_points_zero_constant ha' hb), f3 n a a' b ha ha' hb, smul_add]
    · rw [ev_ratSmul _ (pair_points_zero_constant ha (gp_addOf _ G.const _ _ hb hb')), ev_ratSmul _ (pair_points_zero_constant ha hb),
        ev_ratSmul _ (pair_points_zero_constant ha hb'), f4 n a b b' ha hb hb', smul_add]

variable {O : Type} [CommRing O] {G : FGLaw k d} (A : OAct O G)

def leftMap (c : O) : Module.End ℚ (biadd G) where
  toFun g := ⟨ev ![comp1 (A.act c) (pt k (n := 2) d 0), pt k (n := 2) d 1] (g : PS k 2 d), by
    have hc : GP (A.act c) := A.const c
    obtain ⟨g, g1, g2, g3, g4⟩ := g
    refine ⟨fun n b hb => ?_, fun n a ha => ?_, fun n a a' b ha ha' hb => ?_,
      fun n a b b' ha hb hb' => ?_⟩
    · rw [ev_left _ hc _ _ gp_zero₂ hb, gt_comp1_zero _ hc, g1 n b hb]
    · rw [ev_left _ hc _ _ ha gp_zero₂, g2 n _ (gp_comp1 _ _ hc ha)]
    · rw [ev_left _ hc _ _ (gp_addOf _ G.const _ _ ha ha') hb, ev_left _ hc _ _ ha hb,
        ev_left _ hc _ _ ha' hb, act_addOf A c _ _ ha ha',
        g3 n _ _ _ (gp_comp1 _ _ hc ha) (gp_comp1 _ _ hc ha') hb]
    · rw [ev_left _ hc _ _ ha (gp_addOf _ G.const _ _ hb hb'), ev_left _ hc _ _ ha hb,
        ev_left _ hc _ _ ha hb', g4 n _ _ _ (gp_comp1 _ _ hc ha) hb hb']⟩
  map_add' f g := Subtype.ext
    (gt_ev_add _ (pair_points_zero_constant (gp_comp1 _ _ (A.const c) (gp_pt 0)) (gp_pt 1)) _ _)
  map_smul' q f := Subtype.ext
    (ev_ratSmul _ (pair_points_zero_constant (gp_comp1 _ _ (A.const c) (gp_pt 0)) (gp_pt 1)) _ _)

def rightMap (c : O) : Module.End ℚ (biadd G) where
  toFun g := ⟨ev ![pt k (n := 2) d 0, comp1 (A.act c) (pt k (n := 2) d 1)] (g : PS k 2 d), by
    have hc : GP (A.act c) := A.const c
    obtain ⟨g, g1, g2, g3, g4⟩ := g
    refine ⟨fun n b hb => ?_, fun n a ha => ?_, fun n a a' b ha ha' hb => ?_,
      fun n a b b' ha hb hb' => ?_⟩
    · rw [ev_right _ hc _ _ gp_zero₂ hb, g1 n _ (gp_comp1 _ _ hc hb)]
    · rw [ev_right _ hc _ _ ha gp_zero₂, gt_comp1_zero _ hc, g2 n a ha]
    · rw [ev_right _ hc _ _ (gp_addOf _ G.const _ _ ha ha') hb, ev_right _ hc _ _ ha hb,
        ev_right _ hc _ _ ha' hb, g3 n _ _ _ ha ha' (gp_comp1 _ _ hc hb)]
    · rw [ev_right _ hc _ _ ha (gp_addOf _ G.const _ _ hb hb'), ev_right _ hc _ _ ha hb,
        ev_right _ hc _ _ ha hb', act_addOf A c _ _ hb hb',
        g4 n _ _ _ ha (gp_comp1 _ _ hc hb) (gp_comp1 _ _ hc hb')]⟩
  map_add' f g := Subtype.ext
    (gt_ev_add _ (pair_points_zero_constant (gp_pt 0) (gp_comp1 _ _ (A.const c) (gp_pt 1))) _ _)
  map_smul' q f := Subtype.ext
    (ev_ratSmul _ (pair_points_zero_constant (gp_pt 0) (gp_comp1 _ _ (A.const c) (gp_pt 1))) _ _)

theorem leftMap_val (c : O) (g : biadd G) : (leftMap A c g : PS k 2 d) =
    ev ![comp1 (A.act c) (pt k (n := 2) d 0), pt k (n := 2) d 1] (g : PS k 2 d) := rfl

theorem rightMap_val (c : O) (g : biadd G) : (rightMap A c g : PS k 2 d) =
    ev ![pt k (n := 2) d 0, comp1 (A.act c) (pt k (n := 2) d 1)] (g : PS k 2 d) := rfl

def leftHom : O →+* Module.End ℚ (biadd G) :=
  RingHom.mk'
    { toFun := leftMap A
      map_one' := by
        refine LinearMap.ext fun g => Subtype.ext ?_
        rw [leftMap_val, one_act_apply A _ (gp_pt 0), ev_pt_two]
        rfl
      map_mul' := fun a b => by
        refine LinearMap.ext fun g => Subtype.ext ?_
        rw [Module.End.mul_apply, leftMap_val, leftMap_val, leftMap_val,
          ev_left _ (A.const b) _ _ (gp_comp1 _ _ (A.const a) (gp_pt 0)) (gp_pt 1),
          mul_comm a b, mul_act_apply A _ _ _ (gp_pt 0)] }
    (fun a b => by
      refine LinearMap.ext fun g => Subtype.ext ?_
      change (leftMap A (a + b) g : PS k 2 d) = leftMap A a g + leftMap A b g
      rw [leftMap_val, leftMap_val, leftMap_val, add_act_apply A _ _ _ (gp_pt 0)]
      exact g.2.2.2.1 _ _ _ _ (gp_comp1 _ _ (A.const a) (gp_pt 0))
        (gp_comp1 _ _ (A.const b) (gp_pt 0)) (gp_pt 1))

def rightHom : O →+* Module.End ℚ (biadd G) :=
  RingHom.mk'
    { toFun := rightMap A
      map_one' := by
        refine LinearMap.ext fun g => Subtype.ext ?_
        rw [rightMap_val, one_act_apply A _ (gp_pt 1), ev_pt_two]
        rfl
      map_mul' := fun a b => by
        refine LinearMap.ext fun g => Subtype.ext ?_
        rw [Module.End.mul_apply, rightMap_val, rightMap_val, rightMap_val,
          ev_right _ (A.const b) _ _ (gp_pt 0) (gp_comp1 _ _ (A.const a) (gp_pt 1)),
          mul_comm a b, mul_act_apply A _ _ _ (gp_pt 1)] }
    (fun a b => by
      refine LinearMap.ext fun g => Subtype.ext ?_
      change (rightMap A (a + b) g : PS k 2 d) = rightMap A a g + rightMap A b g
      rw [rightMap_val, rightMap_val, rightMap_val, add_act_apply A _ _ _ (gp_pt 1)]
      exact g.2.2.2.2 _ _ _ _ (gp_pt 0) (gp_comp1 _ _ (A.const a) (gp_pt 1))
        (gp_comp1 _ _ (A.const b) (gp_pt 1)))

theorem left_right_commute (a b : O) : Commute (leftHom A a) (rightHom A b) := by
  refine LinearMap.ext fun g => Subtype.ext ?_
  change (leftMap A a (rightMap A b g) : PS k 2 d) = rightMap A b (leftMap A a g)
  rw [leftMap_val, rightMap_val, rightMap_val, leftMap_val,
    ev_right _ (A.const b) _ _ (gp_comp1 _ _ (A.const a) (gp_pt 0)) (gp_pt 1),
    ev_left _ (A.const a) _ _ (gp_pt 0) (gp_comp1 _ _ (A.const b) (gp_pt 1))]

end Biadd

section Log

variable {k : Type} [CommRing k] [Algebra ℚ k] {d : ℕ} {O : Type} [CommRing O] [StarRing O]
  (B : FB k d O)

theorem expS_inj {n : ℕ} {f g : PS k n d} (hf : constantCoeff f = 0) (hg : constantCoeff g = 0)
    (h : FB.expS k f = FB.expS k g) : f = g := exp_inj hf hg h

omit [Algebra ℚ k] in
theorem ad_const (a : O) : constantCoeff (B.ad a) = 1 := by
  have h := congrArg constantCoeff (B.adjoint_zero_fst a)
  rwa [gt_const_ev_eq _ (pair_points_zero_constant gp_zero₂ (gp_pt 0)), map_one] at h

def logAd (a : O) : PS k 2 d := PowerSeries.subst (B.ad a - 1) (PowerSeries.log k)

theorem logAd_const (a : O) : constantCoeff (logAd B a) = 0 := constantCoeff_logS (ad_const B a)

theorem expS_logAd (a : O) : FB.expS k (logAd B a) = B.ad a := exp_log (ad_const B a)

theorem expS_ev_logAd (c : O) {n : ℕ} (a b : Pt k n d) (ha : GP a) (hb : GP b) :
    FB.expS k (ev ![a, b] (logAd B c)) = ev ![a, b] (B.ad c) := by
  rw [← gt_ev_expS _ (pair_points_zero_constant ha hb) _ (logAd_const B c), expS_logAd]

theorem ev_logAd_const (c : O) {n : ℕ} (a b : Pt k n d) (ha : GP a) (hb : GP b) :
    constantCoeff (ev ![a, b] (logAd B c)) = 0 :=
  gt_const_ev _ (pair_points_zero_constant ha hb) _ (logAd_const B c)

theorem logAd_mem (h1 : B.ph1 = 1) (h2 : B.ph2 = 1) (c : O) : logAd B c ∈ biadd B.G := by
  refine ⟨fun n b hb => ?_, fun n a ha => ?_, fun n a a' b ha ha' hb => ?_,
    fun n a b b' ha hb hb' => ?_⟩
  · refine eq_zero_of_exp_eq_one (ev_logAd_const B c _ _ gp_zero₂ hb) ?_
    refine (expS_ev_logAd B c _ _ gp_zero₂ hb).trans ?_
    have h := congrArg (ev ![b]) (B.adjoint_zero_fst c)
    rw [ev_ev_two _ (single_point_zero_constant hb) _ _ gp_zero₂ (gp_pt 0), evP_zero _ (single_point_zero_constant hb),
      evP_pt _ (single_point_zero_constant hb), ev_one] at h
    exact h
  · refine eq_zero_of_exp_eq_one (ev_logAd_const B c _ _ ha gp_zero₂) ?_
    refine (expS_ev_logAd B c _ _ ha gp_zero₂).trans ?_
    have h := congrArg (ev ![a]) (B.adjoint_zero_snd c)
    rw [ev_ev_two _ (single_point_zero_constant ha) _ _ (gp_pt 0) gp_zero₂, evP_zero _ (single_point_zero_constant ha),
      evP_pt _ (single_point_zero_constant ha), ev_one] at h
    exact h
  · have hs := gp_addOf _ B.G.const _ _ ha ha'
    have hV := triple_points_zero_constant ha ha' hb
    refine expS_inj (ev_logAd_const B c _ _ hs hb)
      (by rw [map_add, ev_logAd_const B c _ _ ha hb, ev_logAd_const B c _ _ ha' hb, add_zero]) ?_
    rw [gt_expS_add _ _ (ev_logAd_const B c _ _ ha hb) (ev_logAd_const B c _ _ ha' hb),
      expS_ev_logAd B c _ _ hs hb, expS_ev_logAd B c _ _ ha hb, expS_ev_logAd B c _ _ ha' hb]
    have h := B.adjoint_compat_left c
    rw [h1, ev_one, ev_one, one_mul, mul_one] at h
    have h' := congrArg (ev ![a, a', b]) h
    rw [gt_ev_mul _ hV,
      ev_ev_two _ hV _ _ (gp_addOf _ B.G.const _ _ (gp_pt 0) (gp_pt 1)) (gp_pt 2),
      ev_ev_two _ hV _ _ (gp_pt 0) (gp_pt 2), ev_ev_two _ hV _ _ (gp_pt 1) (gp_pt 2),
      evP_addOf _ hV _ _ _ (gp_pt 0) (gp_pt 1), evP_pt _ hV, evP_pt _ hV,
      evP_pt _ hV] at h'
    exact h'
  · have hs := gp_addOf _ B.G.const _ _ hb hb'
    have hV := triple_points_zero_constant ha hb hb'
    refine expS_inj (ev_logAd_const B c _ _ ha hs)
      (by rw [map_add, ev_logAd_const B c _ _ ha hb, ev_logAd_const B c _ _ ha hb', add_zero]) ?_
    rw [gt_expS_add _ _ (ev_logAd_const B c _ _ ha hb) (ev_logAd_const B c _ _ ha hb'),
      expS_ev_logAd B c _ _ ha hs, expS_ev_logAd B c _ _ ha hb, expS_ev_logAd B c _ _ ha hb']
    have h := B.adjoint_compat_right c
    rw [h2, ev_one, ev_one, one_mul, mul_one] at h
    have h' := congrArg (ev ![a, b, b']) h
    rw [gt_ev_mul _ hV,
      ev_ev_two _ hV _ _ (gp_pt 0) (gp_addOf _ B.G.const _ _ (gp_pt 1) (gp_pt 2)),
      ev_ev_two _ hV _ _ (gp_pt 0) (gp_pt 1), ev_ev_two _ hV _ _ (gp_pt 0) (gp_pt 2),
      evP_addOf _ hV _ _ _ (gp_pt 1) (gp_pt 2), evP_pt _ hV, evP_pt _ hV,
      evP_pt _ hV] at h'
    exact h'

theorem logAd_add (h1 : B.ph1 = 1) (h2 : B.ph2 = 1) (a b : O) :
    logAd B (a + b) = logAd B a + logAd B b := by
  refine expS_inj (logAd_const B _) (by rw [map_add, logAd_const, logAd_const, add_zero]) ?_
  rw [gt_expS_add _ _ (logAd_const B a) (logAd_const B b), expS_logAd, expS_logAd, expS_logAd]
  have h := B.ad_add a b
  rwa [h1, h2, ev_one, ev_one, one_mul, mul_one] at h

theorem logAd_mul (a b : O) : logAd B (a * b) =
    ev ![comp1 (B.A.act b) (pt k (n := 2) d 0), pt k (n := 2) d 1] (logAd B a) +
      ev ![pt k (n := 2) d 0, comp1 (B.A.act (star a)) (pt k (n := 2) d 1)] (logAd B b) := by
  have hx : GP (comp1 (B.A.act b) (pt k (n := 2) d 0)) :=
    gp_comp1 _ _ (B.A.const b) (gp_pt 0)
  have hz : GP (comp1 (B.A.act (star a)) (pt k (n := 2) d 1)) :=
    gp_comp1 _ _ (B.A.const _) (gp_pt 1)
  have c1 := ev_logAd_const B a _ _ hx (gp_pt 1)
  have c2 := ev_logAd_const B b _ _ (gp_pt 0) hz
  refine expS_inj (logAd_const B _) (by rw [map_add, c1, c2, add_zero]) ?_
  rw [gt_expS_add _ _ c1 c2, expS_logAd, expS_ev_logAd B a _ _ hx (gp_pt 1),
    expS_ev_logAd B b _ _ (gp_pt 0) hz, B.ad_mul]

end Log

theorem exists_action_gauge :
    (∀ (O : Type) [CommRing O] [Module.Free ℤ O] [Module.Finite ℤ O] [IsReduced O] (V : Type) [AddCommGroup V] [Module ℚ V] (l r : O →+* Module.End ℚ V), (∀ a b, Commute (l a) (r b)) → ∀ δ : O →+ V, (∀ a b, δ (a * b) = l b (δ a) + r a (δ b)) → ∃ v : V, ∀ a, δ a = l a v - r a v) → ∀ (k : Type) [CommRing k] [Algebra ℚ k] (d : ℕ) (O : Type) [CommRing O] [StarRing O] [Module.Free ℤ O] [Module.Finite ℤ O] [IsReduced O] (B : FB k d O), B.ph1 = 1 → B.ph2 = 1 → ∃ h : PS k 2 d, (ev (n := 1) ![0, pt k d 0] h = 0 ∧ ev (n := 1) ![pt k d 0, 0] h = 0) ∧ (ev (n := 3) ![pt k d 0, pt k d 2] h + ev (n := 3) ![pt k d 1, pt k d 2] h - ev (n := 3) ![addOf B.G.F (pt k d 0) (pt k d 1), pt k d 2] h) = 0 ∧ (ev (n := 3) ![pt k d 0, pt k d 1] h + ev (n := 3) ![pt k d 0, pt k d 2] h - ev (n := 3) ![pt k d 0, addOf B.G.F (pt k d 1) (pt k d 2)] h) = 0 ∧ ∀ a : O, B.ad a = FB.expS k (ev (n := 2) ![comp1 (B.A.act a) (pt k d 0), pt k d 1] h - ev (n := 2) ![pt k d 0, comp1 (B.A.act (star a)) (pt k d 1)] h) := by
  intro H k _ _ d O _ _ _ _ _ B h1 h2
  let δ : O →+ biadd B.G := AddMonoidHom.mk' (fun a => ⟨logAd B a, logAd_mem B h1 h2 a⟩)
    (fun a b => Subtype.ext (logAd_add B h1 h2 a b))
  obtain ⟨v, hv⟩ := H O (biadd B.G) (leftHom B.A) ((rightHom B.A).comp (starRingEnd O))
    (fun a b => left_right_commute B.A a (star b)) δ (fun a b => Subtype.ext (logAd_mul B a b))
  refine ⟨v, ⟨v.2.1 _ _ (gp_pt 0), v.2.2.1 _ _ (gp_pt 0)⟩, ?_, ?_, fun a => ?_⟩
  · rw [v.2.2.2.1 _ _ _ _ (gp_pt 0) (gp_pt 1) (gp_pt 2), sub_self]
  · rw [v.2.2.2.2 _ _ _ _ (gp_pt 0) (gp_pt 1) (gp_pt 2), sub_self]
  · rw [← expS_logAd B a]
    exact congrArg (FB.expS k) (congrArg Subtype.val (hv a))

end GlobalTheory.ActionGauge
