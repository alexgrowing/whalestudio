import Development.WeilBound.CoreStatements.HodgeTatePoints.CbBase

noncomputable section

namespace PositivityTheory.HtPt.Cb

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
open ReciprocityTheory.ChartRestriction.G.TB

section

variable {R : Type} [CommRing R] {d n : ℕ} {O : Type} [CommRing O] [StarRing O] (B : FB R d O)
variable {x y z w : Pt R n d}

theorem first_form_zero_left (hy : Z y) (hz : Z z) : ev ![0, y, z] B.ph1 = 1 := by
  have hb : ZZ ![y, z] := ZZ_cons hy (ZZ_cons hz ZZ_nil)
  have h := congrArg (ev ![y, z]) B.cocycleLeft_zero_fst
  rw [ev3 hb Z_zero (Z_pt _) (Z_pt _), ep_zero hb, ev_one] at h
  simpa [ep_pt hb] using h

theorem first_form_zero_right (hy : Z y) (hz : Z z) : ev ![y, z, 0] B.ph1 = 1 := by
  have hb : ZZ ![y, z] := ZZ_cons hy (ZZ_cons hz ZZ_nil)
  have h := congrArg (ev ![y, z]) B.cocycleLeft_zero_thd
  rw [ev3 hb (Z_pt _) (Z_pt _) Z_zero, ep_zero hb, ev_one] at h
  simpa [ep_pt hb] using h

theorem first_form_comm_at (hx : Z x) (hy : Z y) (hz : Z z) : ev ![x, y, z] B.ph1 = ev ![y, x, z] B.ph1 := by
  have hb : ZZ ![x, y, z] := ZZ_cons hx (ZZ_cons hy (ZZ_cons hz ZZ_nil))
  have h := congrArg (ev ![x, y, z]) B.cocycleLeft_comm
  rw [ev3 hb (Z_pt _) (Z_pt _) (Z_pt _)] at h
  simp only [ep_pt hb] at h
  simpa using h.symm

theorem first_form_assoc_at (hx : Z x) (hy : Z y) (hw : Z w) (hz : Z z) :
    ev ![x, y, z] B.ph1 * ev ![B.G.add x y, w, z] B.ph1 = ev ![y, w, z] B.ph1 * ev ![x, B.G.add y w, z] B.ph1 := by
  have hb : ZZ ![x, y, w, z] := ZZ_cons hx (ZZ_cons hy (ZZ_cons hw (ZZ_cons hz ZZ_nil)))
  have h := congrArg (ev ![x, y, w, z]) B.cocycleLeft_assoc
  simp only [evm hb] at h
  rw [ev3 hb (Z_pt _) (Z_pt _) (Z_pt _), ev3 hb (Z_add _ (Z_pt _) (Z_pt _)) (Z_pt _) (Z_pt _),
    ev3 hb (Z_pt _) (Z_pt _) (Z_pt _), ev3 hb (Z_pt _) (Z_add _ (Z_pt _) (Z_pt _)) (Z_pt _),
    ep_add _ hb (Z_pt _) (Z_pt _), ep_add _ hb (Z_pt _) (Z_pt _)] at h
  simp only [ep_pt hb] at h
  simpa using h

private theorem fgLaw_add_comm (G : FGLaw R d) (hx : Z x) (hy : Z y) : G.add x y = G.add y x := by
  have hb : ZZ ![x, y] := ZZ_cons hx (ZZ_cons hy ZZ_nil)
  have e : G.add (pt R d 1) (pt R d 0) = (G.add (pt R d 0) (pt R d 1) : Pt R 2 d) := by
    funext i
    exact (G.comm i).trans (eval_points_two _).symm
  have h := congrArg (ep ![x, y]) e
  rw [ep_add G hb (Z_pt _) (Z_pt _), ep_add G hb (Z_pt _) (Z_pt _)] at h
  simpa [ep_pt hb] using h.symm

private theorem fgLaw_add_assoc (G : FGLaw R d) (hx : Z x) (hy : Z y) (hz : Z z) :
    G.add (G.add x y) z = G.add x (G.add y z) := by
  have hb : ZZ ![x, y, z] := ZZ_cons hx (ZZ_cons hy (ZZ_cons hz ZZ_nil))
  have e : G.add (G.add (pt R d 0) (pt R d 1)) (pt R d 2) =
      (G.add (pt R d 0) (G.add (pt R d 1) (pt R d 2)) : Pt R 3 d) := by
    funext i
    exact G.assoc i
  have h := congrArg (ep ![x, y, z]) e
  rw [ep_add G hb (Z_add _ (Z_pt _) (Z_pt _)) (Z_pt _), ep_add G hb (Z_pt _) (Z_pt _),
    ep_add G hb (Z_pt _) (Z_add _ (Z_pt _) (Z_pt _)), ep_add G hb (Z_pt _) (Z_pt _)] at h
  simpa [ep_pt hb] using h

theorem first_form_four_term {a b c e : Pt R n d} (ha : Z a) (hb : Z b) (hc : Z c) (he : Z e) (hz : Z z) :
    ev ![a, b, z] B.ph1 * ev ![c, e, z] B.ph1 * ev ![B.G.add a b, B.G.add c e, z] B.ph1 =
      ev ![a, c, z] B.ph1 * ev ![b, e, z] B.ph1 * ev ![B.G.add a c, B.G.add b e, z] B.ph1 := by
  have A1 := first_form_assoc_at B (Z_add B.G ha hb) hc he hz
  have A2 := first_form_assoc_at B ha hb hc hz
  have A3 := first_form_assoc_at B (Z_add B.G ha hc) hb he hz
  have A4 := first_form_assoc_at B ha hc hb hz
  have e1 : B.G.add c b = B.G.add b c := fgLaw_add_comm B.G hc hb
  have e2 : B.G.add (B.G.add a c) b = B.G.add (B.G.add a b) c := by
    rw [fgLaw_add_assoc B.G ha hc hb, e1, ← fgLaw_add_assoc B.G ha hb hc]
  rw [e1, first_form_comm_at B hc hb hz] at A4
  rw [e2] at A3
  linear_combination ev ![B.G.add (B.G.add a b) c, e, z] B.ph1 * A2 -
    ev ![B.G.add (B.G.add a b) c, e, z] B.ph1 * A4 - ev ![a, b, z] B.ph1 * A1 + ev ![a, c, z] B.ph1 * A3

theorem first_power_eq_prod_at (hx : Z x) (hz : Z z) (k : ℕ) :
    ev ![x, z] (pow1 B k) = ∏ j ∈ Finset.range k, ev ![comp1 (B.A.act (j : O)) x, x, z] B.ph1 := by
  rw [pow1]
  evs

private theorem comp1_act_natCast_zero (hx : Z x) : comp1 (B.A.act ((0 : ℕ) : O)) x = 0 := by
  rw [Nat.cast_zero, act_zero]
  funext i
  exact evz (ZZ_cons hx ZZ_nil)

private theorem comp1_act_natCast_succ (hx : Z x) (k : ℕ) :
    comp1 (B.A.act ((k + 1 : ℕ) : O)) x = B.G.add (comp1 (B.A.act (k : O)) x) x := by
  rw [Nat.cast_succ, PositivityTheory.HtPt.Cb.add_act B.A _ _ hx, B.A.one_act]
  congr 1
  exact ep_pt (ZZ_cons hx ZZ_nil) 0

private theorem ev_pow1_succ (hx : Z x) (hz : Z z) (k : ℕ) :
    ev ![x, z] (pow1 B (k + 1)) = ev ![x, z] (pow1 B k) * ev ![comp1 (B.A.act (k : O)) x, x, z] B.ph1 := by
  rw [first_power_eq_prod_at B hx hz, first_power_eq_prod_at B hx hz, Finset.prod_range_succ]

theorem first_power_add_at (hx : Z x) (hy : Z y) (hz : Z z) (k : ℕ) :
    ev ![B.G.add x y, z] (pow1 B k) * ev ![x, y, z] B.ph1 ^ k =
      ev ![x, z] (pow1 B k) * ev ![y, z] (pow1 B k) *
        ev ![comp1 (B.A.act (k : O)) x, comp1 (B.A.act (k : O)) y, z] B.ph1 := by
  induction k with
  | zero =>
    rw [first_power_eq_prod_at B (Z_add B.G hx hy) hz, first_power_eq_prod_at B hx hz, first_power_eq_prod_at B hy hz, Finset.prod_range_zero,
      comp1_act_natCast_zero B hx, comp1_act_natCast_zero B hy, first_form_zero_left B Z_zero hz]
    simp
  | succ k ih =>
    have hkx : Z (comp1 (B.A.act (k : O)) x) := Z_comp1 (Z_act _ _) hx
    have hky : Z (comp1 (B.A.act (k : O)) y) := Z_comp1 (Z_act _ _) hy
    have h4 := first_form_four_term B hkx hky hx hy hz
    rw [ev_pow1_succ B (Z_add B.G hx hy) hz, ev_pow1_succ B hx hz, ev_pow1_succ B hy hz,
      comp1_act_natCast_succ B hx, comp1_act_natCast_succ B hy, act_add B.A _ hx hy]
    linear_combination ev ![x, y, z] B.ph1 *
        ev ![B.G.add (comp1 (B.A.act (k : O)) x) (comp1 (B.A.act (k : O)) y), B.G.add x y, z] B.ph1 * ih +
      ev ![x, z] (pow1 B k) * ev ![y, z] (pow1 B k) * h4

theorem adjoint_law_first_at (a : O) (hx : Z x) (hy : Z y) (hz : Z z) :
    ev ![comp1 (B.A.act a) x, comp1 (B.A.act a) y, z] B.ph1 * ev ![B.G.add x y, z] (B.ad a) =
      ev ![x, z] (B.ad a) * ev ![y, z] (B.ad a) * ev ![x, y, comp1 (B.A.act (star a)) z] B.ph1 := by
  have hb : ZZ ![x, y, z] := ZZ_cons hx (ZZ_cons hy (ZZ_cons hz ZZ_nil))
  have h := congrArg (ev ![x, y, z]) (B.adjoint_compat_left a)
  simp only [evm hb] at h
  rw [ev3 hb (Z_comp1 (Z_act _ _) (Z_pt _)) (Z_comp1 (Z_act _ _) (Z_pt _)) (Z_pt _),
    ev2 hb (Z_add _ (Z_pt _) (Z_pt _)) (Z_pt _), ev2 hb (Z_pt _) (Z_pt _), ev2 hb (Z_pt _) (Z_pt _),
    ev3 hb (Z_pt _) (Z_pt _) (Z_comp1 (Z_act _ _) (Z_pt _)),
    ep_comp1 _ hb (Z_pt _), ep_comp1 _ hb (Z_pt _), ep_comp1 _ hb (Z_pt _),
    ep_add _ hb (Z_pt _) (Z_pt _)] at h
  simp only [ep_pt hb] at h
  simpa using h

theorem ad_zero_left (a : O) (hz : Z z) : ev ![0, z] (B.ad a) = 1 := by
  have hb : ZZ ![z] := ZZ_cons hz ZZ_nil
  have h := congrArg (ev ![z]) (B.adjoint_zero_fst a)
  rw [ev2 hb Z_zero (Z_pt _), ep_zero hb, ev_one] at h
  simpa [ep_pt hb] using h

theorem first_power_adjoint_at (a : O) (hx : Z x) (hz : Z z) (k : ℕ) :
    ev ![comp1 (B.A.act a) x, z] (pow1 B k) * ev ![comp1 (B.A.act (k : O)) x, z] (B.ad a) =
      ev ![x, z] (B.ad a) ^ k * ev ![x, comp1 (B.A.act (star a)) z] (pow1 B k) := by
  induction k with
  | zero =>
    rw [first_power_eq_prod_at B (Z_comp1 (Z_act _ _) hx) hz, first_power_eq_prod_at B hx (Z_comp1 (Z_act _ _) hz), Finset.prod_range_zero,
      Finset.prod_range_zero, comp1_act_natCast_zero B hx, ad_zero_left B a hz]
    simp
  | succ k ih =>
    have hkx : Z (comp1 (B.A.act (k : O)) x) := Z_comp1 (Z_act _ _) hx
    have law := adjoint_law_first_at B a hkx hx hz
    rw [ev_pow1_succ B (Z_comp1 (Z_act _ _) hx) hz, ev_pow1_succ B hx (Z_comp1 (Z_act _ _) hz),
      comp1_act_natCast_succ B hx, act_comm B.A (k : O) a hx]
    linear_combination ev ![comp1 (B.A.act a) x, z] (pow1 B k) * law +
      ev ![x, z] (B.ad a) * ev ![comp1 (B.A.act (k : O)) x, x, comp1 (B.A.act (star a)) z] B.ph1 * ih

theorem first_power_zero_left (hz : Z z) (k : ℕ) : ev ![0, z] (pow1 B k) = 1 := by
  rw [first_power_eq_prod_at B Z_zero hz]
  apply Finset.prod_eq_one
  intro j _
  rw [germComp1_zero_of_noConstantCoeff (Z_act _ _)]
  exact first_form_zero_left B Z_zero hz

theorem first_power_zero_right (hx : Z x) (k : ℕ) : ev ![x, 0] (pow1 B k) = 1 := by
  rw [first_power_eq_prod_at B hx Z_zero]
  exact Finset.prod_eq_one fun j _ => first_form_zero_right B (by zz) hx

end

theorem first_power_add : ∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB R d O) (n : ℕ), ev (n := 3) ![B.G.add (pt R d 0) (pt R d 1), pt R d 2] (pow1 B n) * B.ph1 ^ n = ev (n := 3) ![pt R d 0, pt R d 2] (pow1 B n) * ev (n := 3) ![pt R d 1, pt R d 2] (pow1 B n) * ev (n := 3) ![comp1 (B.A.act (n : O)) (pt R d 0), comp1 (B.A.act (n : O)) (pt R d 1), pt R d 2] B.ph1 := by
  intro R _ d O _ _ B n
  have h := first_power_add_at B (Z_pt (n := 3) 0) (Z_pt 1) (Z_pt 2) n
  rwa [eval_points_three] at h

theorem first_power_adjoint : ∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB R d O) (a : O) (n : ℕ), ev (n := 2) ![comp1 (B.A.act a) (pt R d 0), pt R d 1] (pow1 B n) * ev (n := 2) ![comp1 (B.A.act (n : O)) (pt R d 0), pt R d 1] (B.ad a) = B.ad a ^ n * ev (n := 2) ![pt R d 0, comp1 (B.A.act (star a)) (pt R d 1)] (pow1 B n) := by
  intro R _ d O _ _ B a n
  have h := first_power_adjoint_at B a (Z_pt (n := 2) 0) (Z_pt 1) n
  rwa [eval_points_two] at h

end PositivityTheory.HtPt.Cb
