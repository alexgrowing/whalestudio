import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.ChartChg
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.WickOperatorVanishing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.GEWick
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.GaugeTrans
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.CalcExp
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.NatCastMulCoeffOfPderivEq

set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing

namespace GlobalTheory.SecondLawGauge

variable {k : Type} [CommRing k] {d : ℕ}

theorem gp4 {n : ℕ} {a b c e : Pt k n d} (ha : GP a) (hb : GP b) (hc : GP c) (he : GP e) :
    ∀ j, GP (![a, b, c, e] j) := by
  intro j; fin_cases j; exacts [ha, hb, hc, he]

theorem gp_add (G : FGLaw k d) {n : ℕ} {a b : Pt k n d} (ha : GP a) (hb : GP b) : GP (addOf G.F a b) :=
  gp_addOf _ G.const _ _ ha hb

theorem germEv_germEv_two_points {m n : ℕ} (V : Fin m → Pt k n d) (a b : Pt k m d) (hV : ∀ j, GP (V j)) (ha : GP a)
    (hb : GP b) (f : PS k 2 d) : ev V (ev ![a, b] f) = ev ![evP V a, evP V b] f := by
  rw [gt_ev_ev' V _ hV (pair_points_zero_constant ha hb), eval_pair_points]

theorem germEv_germEv_three_points {m n : ℕ} (V : Fin m → Pt k n d) (a b c : Pt k m d) (hV : ∀ j, GP (V j)) (ha : GP a)
    (hb : GP b) (hc : GP c) (f : PS k 3 d) :
    ev V (ev ![a, b, c] f) = ev ![evP V a, evP V b, evP V c] f := by
  rw [gt_ev_ev' V _ hV (triple_points_zero_constant ha hb hc)]
  congr 1
  funext j; fin_cases j <;> rfl

theorem ev_self3 (f : PS k 3 d) : ev (n := 3) ![pt k d 0, pt k d 1, pt k d 2] f = f := by
  change MvPowerSeries.subst (fun p : Fin 3 × Fin d => (![pt k (n := 3) d 0, pt k d 1, pt k d 2] p.1) p.2) f = f
  have e : (fun p : Fin 3 × Fin d => (![pt k (n := 3) d 0, pt k d 1, pt k d 2] p.1) p.2) = X := by
    funext p
    obtain ⟨j, i⟩ := p
    fin_cases j <;> rfl
  rw [e, MvPowerSeries.subst_self]
  rfl

theorem pderiv_ev {m n : ℕ} (V : Fin m → Pt k n d) (hV : ∀ j, GP (V j)) (f : PS k m d)
    (v : Fin n × Fin d) :
    pderiv k v (ev V f) = ∑ j : Fin m, ∑ l : Fin d, ev V (pderiv k (j, l) f) * pderiv k v (V j l) := by
  unfold ev
  rw [GlobalTheory.FormalCalc.pderiv_subst (gt_hasSubst V hV), Fintype.sum_prod_type]

theorem pderiv_pt_ne {n : ℕ} {a b : Fin n} (h : b ≠ a) (i l : Fin d) :
    pderiv k (a, i) (pt k d b l) = 0 := by
  unfold pt
  rw [pderiv_X_of_ne]
  intro e
  exact h (congrArg Prod.fst e)

theorem pderiv_addOf_zero {n : ℕ} (F : Fin d → PS k 2 d) (a b : Pt k n d) (ha : GP a) (hb : GP b)
    (v : Fin n × Fin d) (h1 : ∀ l, pderiv k v (a l) = 0) (h2 : ∀ l, pderiv k v (b l) = 0) (l : Fin d) :
    pderiv k v (addOf F a b l) = 0 := by
  unfold addOf
  rw [pderiv_ev _ (pair_points_zero_constant ha hb), Fin.sum_univ_two]
  simp [h1, h2]

theorem pderiv_ev_fst {n : ℕ} (a : Fin n) (y : Pt k n d) (hy : GP y) (i : Fin d)
    (h : ∀ l, pderiv k (a, i) (y l) = 0) (f : PS k 2 d) :
    pderiv k (a, i) (ev ![pt k d a, y] f) = ev ![pt k d a, y] (pderiv k ((0 : Fin 2), i) f) := by
  rw [pderiv_ev _ (pair_points_zero_constant (gp_pt a) hy), Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, h, mul_zero, Finset.sum_const_zero, add_zero]
  rw [Finset.sum_eq_single i]
  · simp [pt]
  · intro l _ hl
    unfold pt
    rw [pderiv_X_of_ne, mul_zero]
    intro e
    exact hl (congrArg Prod.snd e)
  · simp

theorem addOf_zero_left (G : FGLaw k d) {n : ℕ} (b : Pt k n d) (hb : GP b) : addOf G.F 0 b = b := by
  funext i
  have := congrArg (ev ![b]) (G.unit i)
  rw [germEv_germEv_two_points _ _ _ (single_point_zero_constant hb) gp_zero₂ (gp_pt _), evP_zero _ (single_point_zero_constant hb),
    evP_pt _ (single_point_zero_constant hb), gt_ev_X _ (single_point_zero_constant hb)] at this
  exact this

local macro "gp" : tactic =>
  `(tactic| repeat' (first
    | assumption | exact gp_pt _ | exact gp_zero₂ | apply gp_add | apply single_point_zero_constant | apply pair_points_zero_constant
    | apply triple_points_zero_constant | apply gp4))

local macro "push_ev" loc:(Lean.Parser.Tactic.location)? : tactic =>
  `(tactic| simp (disch := gp) only [germEv_germEv_two_points, germEv_germEv_three_points, gt_ev_add, gt_ev_sub, gt_ev_mul, gt_ev_zero, ev_one,
    evP_pt, evP_addOf, evP_zero, Matrix.cons_val] $[$loc]?)

theorem exists_gauge_second_law : (∀ (k : Type) [CommRing k] [Algebra ℚ k] (d : ℕ) (G : FGLaw k d) (c : PS k 3 d), ev (n := 2) ![0, pt k d 0, pt k d 1] c = 0 → ev (n := 3) ![pt k d 1, pt k d 0, pt k d 2] c = c → ev (n := 4) ![pt k d 0, pt k d 1, pt k d 3] c + ev (n := 4) ![addOf G.F (pt k d 0) (pt k d 1), pt k d 2, pt k d 3] c = ev (n := 4) ![pt k d 1, pt k d 2, pt k d 3] c + ev (n := 4) ![pt k d 0, addOf G.F (pt k d 1) (pt k d 2), pt k d 3] c → ∃ h : PS k 2 d, ev (n := 1) ![0, pt k d 0] h = 0 ∧ (∀ i, ev (n := 1) ![0, pt k d 0] (pderiv k ((0 : Fin 2), i) h) = 0) ∧ c = (ev (n := 3) ![pt k d 0, pt k d 2] h + ev (n := 3) ![pt k d 1, pt k d 2] h - ev (n := 3) ![addOf G.F (pt k d 0) (pt k d 1), pt k d 2] h)) → (∀ (k : Type) [CommRing k] [Algebra ℚ k] (d : ℕ) (G : FGLaw k d) (q : ℕ) (g : PS k (q + 1) d), ev (n := q + 2) (Fin.cons (addOf G.F (pt k d 0) (pt k d 1)) (fun j : Fin q => pt k d j.succ.succ)) g = ev (n := q + 2) (Fin.cons (pt k d 0) (fun j : Fin q => pt k d j.succ.succ)) g + ev (n := q + 2) (Fin.cons (pt k d 1) (fun j : Fin q => pt k d j.succ.succ)) g → (∀ i, ev (n := q) (Fin.cons 0 (fun j : Fin q => pt k d j)) (pderiv k ((0 : Fin (q + 1)), i) g) = 0) → g = 0) → ∀ (k : Type) [CommRing k] [Algebra ℚ k] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB k d O), B.ph1 = 1 → ∃ h : PS k 2 d, (ev (n := 1) ![0, pt k d 0] h = 0 ∧ ev (n := 1) ![pt k d 0, 0] h = 0) ∧ (ev (n := 3) ![pt k d 0, pt k d 2] h + ev (n := 3) ![pt k d 1, pt k d 2] h - ev (n := 3) ![addOf B.G.F (pt k d 0) (pt k d 1), pt k d 2] h) = 0 ∧ B.ph2 = FB.expS k (ev (n := 3) ![pt k d 0, pt k d 1] h + ev (n := 3) ![pt k d 0, pt k d 2] h - ev (n := 3) ![pt k d 0, addOf B.G.F (pt k d 1) (pt k d 2)] h) := by
  intro H1 H2 k _ _ d O _ _ B hB
  have c1 : constantCoeff B.ph2 = 1 := by
    have := congrArg constantCoeff B.cocycleRight_zero_fst
    rwa [gt_const_ev_eq _ (by gp), map_one] at this
  obtain ⟨L, hL0, hL⟩ : ∃ L : PS k 3 d, constantCoeff L = 0 ∧ FB.expS k L = B.ph2 :=
    ⟨_, constantCoeff_logS c1, exp_log c1⟩
  have cL : ∀ {n : ℕ} {a b c : Pt k n d}, GP a → GP b → GP c → constantCoeff (ev ![a, b, c] L) = 0 :=
    fun ha hb hc => gt_const_ev _ (triple_points_zero_constant ha hb hc) _ hL0
  have eL : ∀ {n : ℕ} {a b c : Pt k n d}, GP a → GP b → GP c →
      ev ![a, b, c] B.ph2 = FB.expS k (ev ![a, b, c] L) := by
    intro n a b c ha hb hc
    rw [← hL, gt_ev_expS _ (triple_points_zero_constant ha hb hc) _ hL0]
  have inj : ∀ {n : ℕ} {f g : PS k n d}, constantCoeff f = 0 → constantCoeff g = 0 →
      FB.expS k f = FB.expS k g → f = g := fun hf hg h => exp_inj hf hg h
  have inj2 : ∀ {n : ℕ} {f g f' g' : PS k n d}, constantCoeff f = 0 → constantCoeff g = 0 →
      constantCoeff f' = 0 → constantCoeff g' = 0 →
      FB.expS k f * FB.expS k g = FB.expS k f' * FB.expS k g' → f + g = f' + g' := by
    intro n f g f' g' hf hg hf' hg' h
    refine inj (by simp [hf, hg]) (by simp [hf', hg']) ?_
    rw [gt_expS_add _ _ hf hg, gt_expS_add _ _ hf' hg', h]
  have e0 : ∀ {n : ℕ}, FB.expS k (0 : PS k n d) = 1 := exp_zero
  have Lax : ev (n := 2) ![pt k d 1, 0, pt k d 0] L = 0 := by
    have := congrArg (ev (n := 2) ![pt k d 1, pt k d 0]) B.cocycleRight_zero_snd
    push_ev at this
    refine inj (cL (by gp) (by gp) (by gp)) (map_zero _) ?_
    rw [← eL (by gp) (by gp) (by gp), this, e0]
  have Lcomm : ev (n := 3) ![pt k d 2, pt k d 1, pt k d 0] L =
      ev (n := 3) ![pt k d 2, pt k d 0, pt k d 1] L := by
    have := congrArg (ev (n := 3) ![pt k d 2, pt k d 0, pt k d 1]) B.cocycleRight_comm
    push_ev at this
    refine inj (cL (by gp) (by gp) (by gp)) (cL (by gp) (by gp) (by gp)) ?_
    rw [← eL (by gp) (by gp) (by gp), ← eL (by gp) (by gp) (by gp), this]
  have Lassoc : ev (n := 4) ![pt k d 3, pt k d 0, pt k d 1] L +
      ev (n := 4) ![pt k d 3, addOf B.G.F (pt k d 0) (pt k d 1), pt k d 2] L =
      ev (n := 4) ![pt k d 3, pt k d 1, pt k d 2] L +
      ev (n := 4) ![pt k d 3, pt k d 0, addOf B.G.F (pt k d 1) (pt k d 2)] L := by
    have := congrArg (ev (n := 4) ![pt k d 3, pt k d 0, pt k d 1, pt k d 2]) B.cocycleRight_assoc
    push_ev at this
    refine inj2 (cL (by gp) (by gp) (by gp)) (cL (by gp) (by gp) (by gp))
      (cL (by gp) (by gp) (by gp)) (cL (by gp) (by gp) (by gp)) ?_
    rw [← eL (by gp) (by gp) (by gp), ← eL (by gp) (by gp) (by gp), ← eL (by gp) (by gp) (by gp),
      ← eL (by gp) (by gp) (by gp), this]
  have Lint : ev (n := 4) ![addOf B.G.F (pt k d 2) (pt k d 3), pt k d 0, pt k d 1] L =
      ev (n := 4) ![pt k d 2, pt k d 0, pt k d 1] L + ev (n := 4) ![pt k d 3, pt k d 0, pt k d 1] L := by
    have := congrArg (ev (n := 4) ![pt k d 2, pt k d 3, pt k d 0, pt k d 1]) B.interchange
    rw [hB] at this
    push_ev at this
    rw [← zero_add (ev _ L)]
    refine inj2 (map_zero _) (cL (by gp) (by gp) (by gp))
      (cL (by gp) (by gp) (by gp)) (cL (by gp) (by gp) (by gp)) ?_
    rw [← eL (by gp) (by gp) (by gp), ← eL (by gp) (by gp) (by gp), ← eL (by gp) (by gp) (by gp), e0]
    simpa using this
  obtain ⟨g, g0, g1, hg⟩ := H1 k d B.G (ev (n := 3) ![pt k d 2, pt k d 0, pt k d 1] L)
    (by push_ev; exact Lax) (by push_ev; exact Lcomm) (by push_ev; exact Lassoc)
  have hg' : ∀ {n : ℕ} {x a b : Pt k n d}, GP x → GP a → GP b →
      ev ![x, a, b] L = ev ![a, x] g + ev ![b, x] g - ev ![addOf B.G.F a b, x] g := by
    intro n x a b hx ha hb
    have := congrArg (ev ![a, b, x]) hg
    push_ev at this
    exact this
  have g1' : ∀ {n : ℕ} {x : Pt k n d}, GP x → ∀ i, ev ![0, x] (pderiv k ((0 : Fin 2), i) g) = 0 := by
    intro n x hx i
    have := congrArg (ev ![x]) (g1 i)
    push_ev at this
    exact this
  have hu : ev (n := 3) ![pt k d 0, pt k d 1] g + ev (n := 3) ![pt k d 0, pt k d 2] g -
      ev (n := 3) ![pt k d 0, addOf B.G.F (pt k d 1) (pt k d 2)] g = 0 := by
    refine H2 k d B.G 2 _ ?_ ?_
    · have v : ∀ y : Pt k 4 d, (Fin.cons y (fun j : Fin 2 => pt k d j.succ.succ) : Fin 3 → Pt k 4 d) =
          ![y, pt k d 2, pt k d 3] := by
        intro y; funext j; fin_cases j <;> rfl
      rw [v, v, v]
      push_ev
      rw [hg' (by gp) (by gp) (by gp), hg' (by gp) (by gp) (by gp), hg' (by gp) (by gp) (by gp)] at Lint
      linear_combination Lint
    · intro i
      have v : (Fin.cons 0 (fun j : Fin 2 => pt k d j) : Fin 3 → Pt k 2 d) =
          ![0, pt k d 0, pt k d 1] := by
        funext j; fin_cases j <;> rfl
      rw [v, map_sub, map_add, pderiv_ev_fst _ _ (by gp) _ (pderiv_pt_ne (by decide) i),
        pderiv_ev_fst _ _ (by gp) _ (pderiv_pt_ne (by decide) i),
        pderiv_ev_fst _ _ (by gp) _ (pderiv_addOf_zero _ _ _ (by gp) (by gp) _
          (pderiv_pt_ne (by decide) i) (pderiv_pt_ne (by decide) i))]
      push_ev
      rw [g1' (by gp), g1' (by gp), g1' (by gp)]
      simp
  refine ⟨ev (n := 2) ![pt k d 1, pt k d 0] g, ⟨?_, ?_⟩, ?_, ?_⟩
  · have := congrArg (ev (n := 1) ![pt k d 0, 0, 0]) hu
    push_ev at this
    rw [addOf_zero_left _ _ (by gp), add_sub_cancel_right] at this
    push_ev
    exact this
  · push_ev
    exact g0
  · have := congrArg (ev (n := 3) ![pt k d 2, pt k d 0, pt k d 1]) hu
    push_ev at this
    push_ev
    exact this
  · push_ev
    rw [← hg' (by gp) (by gp) (by gp), ev_self3, hL]

end GlobalTheory.SecondLawGauge
