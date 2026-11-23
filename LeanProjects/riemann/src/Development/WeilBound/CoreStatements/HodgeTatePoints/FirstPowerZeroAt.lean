import Development.WeilBound.CoreStatements.HodgeTatePoints.CcBase

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj

namespace PositivityTheory.HtPt.Cc

variable {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O] (B : FB R d O) {l : ℕ}

theorem pow_sy_at {x z : Pt R l d} (hx : Z x) (hz : Z z) (n : ℕ) :
    ev ![x, z] (pow2 B n) * ev ![x, z] B.sy ^ n =
      ev ![x, comp1 (B.A.act (n : O)) z] B.sy * ev ![z, x] (pow1 B n) := by
  induction n with
  | zero =>
    rw [act_zero_at, symmetric_zero_right_at B hx]
    simp only [second_power_zero, first_power_zero, ev_one, pow_zero, mul_one]
  | succ n ih =>
    rw [second_power_succ_at B n hx hz, first_power_succ_at B n hz hx, act_succ_at B n hz, pow_succ]
    have hl := sy_law_at B hx (Z_comp1 (Z_act B.A (n : O)) hz) hz
    linear_combination (ev ![x, comp1 (B.A.act (n : O)) z, z] B.ph2 * ev ![x, z] B.sy) * ih
      + ev ![z, x] (pow1 B n) * hl

theorem first_power_zero_at {x : Pt R l d} (hx : Z x) (m : ℕ) : ev ![x, 0] (pow1 B m) = 1 := by
  induction m with
  | zero => simp only [first_power_zero, ev_one]
  | succ k ih =>
    rw [first_power_succ_at B k hx Z_zero, ih, first_form_zero_right_at B (Z_comp1 (Z_act _ _) hx) hx, one_mul]

theorem first_power_add_at {x z w : Pt R l d} (hx : Z x) (hz : Z z) (hw : Z w) (m : ℕ) :
    ev ![x, z] (pow1 B m) * ev ![x, w] (pow1 B m) * ev ![comp1 (B.A.act (m : O)) x, z, w] B.ph2 =
      ev ![x, z, w] B.ph2 ^ m * ev ![x, addOf B.G.F z w] (pow1 B m) := by
  induction m with
  | zero => rw [act_zero_at, second_form_zero_left_at B hz hw, first_power_zero, ev_one, ev_one, ev_one]; simp
  | succ m ih =>
    have hm : Z (comp1 (B.A.act (m : O)) x) := by ztac
    rw [first_power_succ_at B m hx hz, first_power_succ_at B m hx hw, first_power_succ_at B m hx (Z_add _ hz hw), act_succ_at B m hx,
      pow_succ]
    have h1 := interchange_at B hm hx hz hw
    linear_combination (ev ![x, z] (pow1 B m) * ev ![x, w] (pow1 B m)) * h1 +
      (ev ![x, z, w] B.ph2 * ev ![comp1 (B.A.act (m : O)) x, x, addOf B.G.F z w] B.ph1) * ih

theorem pow_inter_at {x z : Pt R l d} (hx : Z x) (hz : Z z) (m n : ℕ) :
    ev ![x, z] (pow2 B n) ^ m * ev ![x, comp1 (B.A.act (n : O)) z] (pow1 B m) =
      ev ![x, z] (pow1 B m) ^ n * ev ![comp1 (B.A.act (m : O)) x, z] (pow2 B n) := by
  induction n with
  | zero => rw [act_zero_at, first_power_zero_at B hx, second_power_zero, ev_one, ev_one]; simp
  | succ n ih =>
    have hn : Z (comp1 (B.A.act (n : O)) z) := by ztac
    have hm : Z (comp1 (B.A.act (m : O)) x) := by ztac
    rw [second_power_succ_at B n hx hz, second_power_succ_at B n hm hz, act_succ_at B n hz, pow_succ, mul_pow]
    have h1 := first_power_add_at B hx hn hz m
    linear_combination (-ev ![x, z] (pow2 B n) ^ m) * h1 +
      (ev ![x, z] (pow1 B m) * ev ![comp1 (B.A.act (m : O)) x, comp1 (B.A.act (n : O)) z, z] B.ph2) * ih

private theorem ev_ph1_mul_ev_lam_addOf_of_isIso {B B₂ : FB R d O} {φ ψ : Pt R 1 d} {lam : PS R 2 d} (h : IsIso B B₂ φ ψ lam)
    {X Y z : Pt R l d} (hX : Z X) (hY : Z Y) (hz : Z z) :
    ev ![X, Y, z] B₂.ph1 * ev ![addOf B₂.G.F X Y, z] lam
      = ev ![X, z] lam * ev ![Y, z] lam * ev ![comp1 φ X, comp1 φ Y, comp1 φ z] B.ph1 := by
  have hφ : Z φ := h.c₁
  have hb : ZZ ![X, Y, z] := ZZ_cons hX (ZZ_cons hY (ZZ_cons hz ZZ_nil))
  have e := congrArg (ev ![X, Y, z]) h.ph1
  simp only [FGLaw.add] at e
  simp only [ev_mul' hb] at e
  rw [ev_ev hb (ZZ_cons (Z_add B₂.G (Z_pt 0) (Z_pt 1)) (ZZ_cons (Z_pt 2) ZZ_nil)),
    ev_ev hb (ZZ_cons (Z_pt 0) (ZZ_cons (Z_pt 2) ZZ_nil)),
    ev_ev hb (ZZ_cons (Z_pt 1) (ZZ_cons (Z_pt 2) ZZ_nil)),
    ev_ev hb (ZZ_cons (Z_comp1 hφ (Z_pt 0)) (ZZ_cons (Z_comp1 hφ (Z_pt 1)) (ZZ_cons (Z_comp1 hφ (Z_pt 2)) ZZ_nil)))] at e
  simp only [evV_cons, evV_nil, evalPoints_coordinatePoint hb, evalPoints_add hb _ (Z_pt _) (Z_pt _), evalPoints_comp hb _ (Z_pt _)] at e
  simpa using e

private theorem ev_zero_lam_eq_one_of_isIso {B B₂ : FB R d O} {φ ψ : Pt R 1 d} {lam : PS R 2 d} (h : IsIso B B₂ φ ψ lam)
    {z : Pt R l d} (hz : Z z) : ev ![0, z] lam = 1 := by
  have hb : ZZ ![z] := ZZ_cons hz ZZ_nil
  have e := congrArg (ev ![z]) h.ax.1
  rw [ev_ev hb (ZZ_cons Z_zero (ZZ_cons (Z_pt 0) ZZ_nil)), ev_one] at e
  simpa [evV_cons, evV_nil, evalPoints_zero, evalPoints_coordinatePoint hb] using e

theorem iso_first_power_at {B} {B₂ : FB R d O} {φ ψ : Pt R 1 d} {lam : PS R 2 d} (h : IsIso B B₂ φ ψ lam)
    {x z : Pt R l d} (hx : Z x) (hz : Z z) (n : ℕ) :
    ev ![x, z] (pow1 B₂ n) * ev ![comp1 (B₂.A.act (n : O)) x, z] lam =
      ev ![x, z] lam ^ n * ev ![comp1 φ x, comp1 φ z] (pow1 B n) := by
  have hφ : Z φ := h.c₁
  induction n with
  | zero =>
    rw [act_zero_at, ev_zero_lam_eq_one_of_isIso h hz]
    simp only [first_power_zero, ev_one, pow_zero, mul_one]
  | succ n ih =>
    rw [first_power_succ_at B₂ n hx hz, act_succ_at B₂ n hx, first_power_succ_at B n (Z_comp1 hφ hx) (Z_comp1 hφ hz), pow_succ]
    have hP := ev_ph1_mul_ev_lam_addOf_of_isIso h (Z_comp1 (Z_act B₂.A (n : O)) hx) hx hz
    have hc : comp1 φ (comp1 (B₂.A.act (n : O)) x) = comp1 (B.A.act (n : O)) (comp1 φ x) := by
      rw [← germComp1_germComp1_eq_substitute φ (Z_act B₂.A _) hx, h.act, germComp1_germComp1_eq_substitute _ hφ hx]
    rw [hc] at hP
    linear_combination ev ![x, z] (pow1 B₂ n) * hP
      + (ev ![x, z] lam * ev ![comp1 (B.A.act (n : O)) (comp1 φ x), comp1 φ x, comp1 φ z] B.ph1) * ih

theorem pow_sy : ∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB R d O) (n : ℕ), pow2 B n * B.sy ^ n = ev (n := 2) ![pt R d 0, comp1 (B.A.act (n : O)) (pt R d 1)] B.sy * ev (n := 2) ![pt R d 1, pt R d 0] (pow1 B n) := by
  intro R _ d O _ _ B n
  have e := pow_sy_at B (Z_pt (R := R) (d := d) (0 : Fin 2)) (Z_pt 1) n
  simp only [eval_identity_two] at e
  exact e

theorem pow_inter : ∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB R d O) (m n : ℕ), pow2 B n ^ m * ev (n := 2) ![pt R d 0, comp1 (B.A.act (n : O)) (pt R d 1)] (pow1 B m) = pow1 B m ^ n * ev (n := 2) ![comp1 (B.A.act (m : O)) (pt R d 0), pt R d 1] (pow2 B n) := by
  intro R _ d O _ _ B m n
  have e := pow_inter_at B (Z_pt (R := R) (d := d) (0 : Fin 2)) (Z_pt 1) m n
  simp only [eval_identity_two] at e
  exact e

theorem iso_first_power : ∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB R d O) (B₂ : FB R d O) (φ ψ : Pt R 1 d) (lam : PS R 2 d) (n : ℕ), IsIso B B₂ φ ψ lam → pow1 B₂ n * ev (n := 2) ![comp1 (B₂.A.act (n : O)) (pt R d 0), pt R d 1] lam = lam ^ n * ev (n := 2) ![comp1 φ (pt R d 0), comp1 φ (pt R d 1)] (pow1 B n) := by
  intro R _ d O _ _ B B₂ φ ψ lam n h
  have e := iso_first_power_at h (Z_pt (R := R) (d := d) (0 : Fin 2)) (Z_pt 1) n
  simp only [eval_identity_two] at e
  exact e

end PositivityTheory.HtPt.Cc
