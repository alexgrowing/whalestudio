import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.QuoIff
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.HtValOnSubset
import Development.AbelianVarietyTheory.Definitions.Divisors.UnifOfSpaceEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EntRCloudSub

set_option synthInstance.maxHeartbeats 400000

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop

namespace GlobalTheory.CovTop.WtShape

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m)

theorem laOf_real (τ : Psi p.T.Q.H) (t : D.what₂.Tau) (ht : τ.1 = DV.tauEmb D t) (n : Fin ((dat p i).p + (dat p i).q)) :
    (laOf (dat p i) (wtA (p.κ i)) (p.κ i).n τ n : ℝ) = entR D i t n := by
  rw [← ent_cast, ← laOf_read p i τ t ht n, Rat.cast_intCast]

theorem anchor_real (τ : Psi p.T.Q.H) (t : D.what₂.Tau) (ht : τ.1 = DV.tauEmb D t) :
    (anchor (dat p i) (wtA (p.κ i)) (p.κ i).n (D.R.k - 1) τ : ℝ) = entR D i t (D.R.k - 1 - 1) := by
  have h : D.R.k - 1 - 1 < (dat p i).p + (dat p i).q := by
    have := D.R.m_add_three_le_k
    rw [dat_p]; omega
  unfold anchor
  rw [dif_pos h, laOf_real p i τ t ht]

theorem uW_real (τ : Psi p.T.Q.H) (t : D.what₂.Tau) (ht : τ.1 = DV.tauEmb D t) (n : Fin ((dat p i).p + (dat p i).q)) :
    (uW p i τ n : ℝ) = entR D i t n - entR D i t (D.R.k - 1 - 1) := by
  rw [← laOf_real p i τ t ht n, ← anchor_real p i τ t ht, ← Int.cast_sub]
  rfl

theorem h0_eq : LevelStarExponents.h0 L = (p.h0 : ℝ) := by
  have hm : (0 : ℝ) < D.R.m := by exact_mod_cast p.hm
  unfold LevelStarExponents.h0
  rw [p.hh0]
  field_simp

theorem wtNum_at (P : ParameterChoice' D L) (T : ParamsT D L P) (hS : SizesAt L) (hx8 : 8 ≤ L.sc.x)
    (hy : 3 ≤ L.sc.x ^ (L.sc.eps / 4)) : WtNum p i T.PP := by
  have hk := D.R.m_add_three_le_k
  have hm := D.R.two_le_m
  have hi := i.2
  have hr : D.R.r = D.R.k + D.R.m - 1 := rfl
  have e1 := dat_p p i
  have e2 := dat_q p i
  have e3 := dat_rank p i
  have hD : dimFlag (dat p i) = T.Dp := (dim_eq p i).trans T.Dp_eq.symm
  have hlx : 2 ≤ Real.log L.sc.x := by
    have h1 : Real.log 8 ≤ Real.log L.sc.x := Real.log_le_log (by norm_num) hx8
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow] at h1
    have := Real.log_two_gt_d9
    push_cast at h1
    linarith
  have hL3 : 3 ≤ L.sc.L :=
    hy.trans (Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith [L.sc.eps_pos]))
  have hwin := size_window D L hS hlx ((i : ℕ) + 1) (Nat.le_add_left _ _) i.2
  have hP := forty_le_PP T
  have hPt := (parameterPrecision_le_length_and_rank D L P T (by linarith) (one_le_nWn D L P T)).2
  have hwid := mul_widths_le D L T.PP (by linarith) hS (by linarith) hy
  have hS0 := L.Sc_pos
  have hη0 := L.etaSz_pos
  have h40 : 40 * (L.Sc + L.etaSz) ≤ L.sc.w'' D.R.n := le_trans (mul_le_mul_of_nonneg_right hP (by linarith)) hwid
  have hrη : (D.R.r : ℝ) ≤ L.etaSz := by
    refine le_trans ?_ P.t_le_eta
    exact_mod_cast (by have := D.R.rank_add_five_le; omega : D.R.r ≤ D.R.t)
  have hr0 : (0 : ℝ) ≤ D.R.r := Nat.cast_nonneg _
  have hlen : lenT p i T.PP ≤ T.TO := by
    unfold lenT; rw [hD]; exact Nat.ceil_le.2 (len_le D L P T)
  have hlen' : 4 * T.Dp + 4 ≤ lenT p i T.PP := by
    unfold lenT; rw [hD]; exact len_ge T
  obtain ⟨s1, s2, s3⟩ := spacing_ge T ((i : ℕ) + 1) _ hlen
  obtain ⟨q1, q2, q3⟩ := prod_bounds T _ hlen
  obtain ⟨g1, g2⟩ := gap_le D L P T (lenT p i T.PP) (Nat.cast_nonneg _) (by exact_mod_cast hlen)
  have hh : LevelStarExponents.h0 L ≤ L.etaSz := div_le_self hη0.le (by exact_mod_cast (by omega : 1 ≤ D.R.m))
  have hstep : ∀ t a, a + 1 < D.R.r → ((lenT p i T.PP : ℝ) + T.Dp + 2) * (lenT p i T.PP + T.Dp + 2 + 2 * (D.R.r : ℝ)) + 1 ≤
      sgR D t a - sgR D t (a + 1) := fun t a ha =>
    sgR_step D L P t _ g1 g2
      (fun hm => le_trans g2 (minimalGap_le_first_lowerRowParameter D L P _ (Nat.le_add_left _ _) i.2 t (hwin t).1 hm)) a ha
  have hstep1 : ∀ t a, a + 1 < D.R.r → 1 ≤ sgR D t a - sgR D t (a + 1) := fun t a ha =>
    le_trans (le_add_of_nonneg_left (by positivity)) (hstep t a ha)
  have hent : ∀ t n, n < D.R.r → |entR D i t n| ≤ 3 * L.sc.b := by
    intro t n hn
    obtain ⟨w1, w2⟩ := hwin t
    by_cases h : n < D.R.k - 1
    · obtain ⟨a1, a2⟩ := entR_cloud L i t n h
      rw [abs_le]; constructor <;> linarith
    · have := entR_node L i t n (by omega) hn
      linarith
  have hanc : ∀ t, L.sc.w'' D.R.n - D.R.r ≤ entR D i t (D.R.k - 1 - 1) := fun t => by
    have := (entR_cloud L i t (D.R.k - 1 - 1) (by omega)).1
    linarith [(hwin t).1]
  have hc0 : (0 : ℝ) ≤ cZeroN D ((i : ℕ) + 1) := Nat.cast_nonneg _
  have hT0 : (0 : ℝ) ≤ lenT p i T.PP := Nat.cast_nonneg _
  have hD0 : (0 : ℝ) ≤ T.Dp := Nat.cast_nonneg _
  have eN : ((((dat p i).p + (dat p i).q : ℕ)) : ℝ) = D.R.r := by rw [e3]
  have eZ : ((((dat p i).p + (dat p i).q : ℕ)) : ℤ) = D.R.r := by rw [e3]
  refine ⟨⟨e1, e2, e3⟩, card_psi p, dim_eq p i, cols_eq p i, dom_wtA _, unit_eq p, ?_, ?_, ?_, ?_, fun him => ?_⟩
  · rw [ofRecord_logOm]; exact abs_logOm_le hS hL3
  · intro τ n
    obtain ⟨t, ht⟩ := exists_tau p τ
    rw [laOf_real p i τ t ht]
    have := hent t n (e3 ▸ n.2)
    have := abs_nonneg (entR D i t n)
    linarith
  · intro τ
    obtain ⟨t, ht⟩ := exists_tau p τ
    rw [anchor_real p i τ t ht]
    linarith [hanc t]
  · rw [hD]; exact ⟨q2, q3⟩
  rw [h0_eq p] at s1 s2 s3 q1 hh
  refine ⟨p.h0, L.Sc, L.etaSz, hS0.le, hη0.le, by linarith, by exact_mod_cast s3, by rw [hD]; exact_mod_cast q1, fun u1 => ?_⟩
  refine ⟨show 1 ≤ D.R.k - 1 by omega, show D.R.k - 1 < (dat p i).p by omega, show (dat p i).p < _ by omega,
    show _ - (dat p i).p < (dat p i).p by omega, Int.natCast_nonneg _, fun τ a ha => uWt_anchor _ _ _ _ τ a ha,
    show 4 * dimFlag (dat p i) + 4 ≤ lenT p i T.PP by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show 4 * ((cZeroN D ((i : ℕ) + 1) : ℤ) + 2 * ((dat p i).p + (dat p i).q : ℕ) + lenT p i T.PP + dimFlag (dat p i) + 1) ≤ p.h0 ∧
      24 * (((dat p i).p + (dat p i).q : ℕ) : ℤ) * lenT p i T.PP ≤ p.h0
    rw [hD, eZ]
    exact ⟨by exact_mod_cast s1, by exact_mod_cast s2⟩
  · intro τ a ha
    obtain ⟨t, ht⟩ := exists_tau p τ
    show |(uW p i τ a : ℝ) + (anchor (dat p i) (wtA (p.κ i)) (p.κ i).n (D.R.k - 1) τ : ℝ)| ≤
      L.etaSz + L.Sc + ((dat p i).p + (dat p i).q : ℕ)
    rw [uW_real p i τ t ht, anchor_real p i τ t ht, sub_add_cancel, eN]
    have := entR_node L i t a ha (e3 ▸ a.2)
    linarith
  · intro τ a ha
    obtain ⟨t, ht⟩ := exists_tau p τ
    show 0 ≤ uW p i τ a ∧ (uW p i τ a : ℝ) ≤ L.Sc
    obtain ⟨a1, a2⟩ := entR_cloud_sub L i t (hstep1 t) a ha
    rw [← uW_real p i τ t ht] at a1 a2
    exact ⟨by exact_mod_cast a1, a2⟩
  · intro τ
    obtain ⟨t, ht⟩ := exists_tau p τ
    show 4 * ((L.etaSz + L.Sc + ((dat p i).p + (dat p i).q : ℕ)) + L.Sc + ((cZeroN D ((i : ℕ) + 1) : ℤ) : ℝ) +
      2 * ((dat p i).p + (dat p i).q : ℕ)) + 20 * ((dat p i).p + (dat p i).q : ℕ) * (lenT p i T.PP : ℝ) ≤
      (anchor (dat p i) (wtA (p.κ i)) (p.κ i).n (D.R.k - 1) τ : ℝ)
    rw [anchor_real p i τ t ht, eN, Int.cast_natCast]
    have := hanc t
    have h5 : 0 ≤ (D.R.r : ℝ) * lenT p i T.PP := by positivity
    nlinarith
  · intro τ a b hab
    obtain ⟨t, ht⟩ := exists_tau p τ
    have hb := b.2
    have hd : ((uW p i τ a - uW p i τ b : ℤ) : ℝ) =
        sgR D t a - sgR D t (a + 1) - 1 + if (a : ℕ) + 1 = D.R.k + i then (D.R.r : ℝ) else 0 := by
      rw [Int.cast_sub, uW_real p i τ t ht, uW_real p i τ t ht, hab, ← entR_step]; ring
    have hge : sgR D t a - sgR D t (a + 1) - 1 ≤ ((uW p i τ a - uW p i τ b : ℤ) : ℝ) := by
      rw [hd]; split_ifs <;> linarith
    refine ⟨fun _ => ?_, fun ha => ?_, fun hp => ?_⟩
    · show ((lenT p i T.PP : ℤ) + dimFlag (dat p i) + 2) *
        ((lenT p i T.PP : ℤ) + dimFlag (dat p i) + 2 + 2 * ((dat p i).p + (dat p i).q : ℕ)) ≤ uW p i τ a - uW p i τ b + 2
      rw [hD, eZ]
      have := hstep t a (by omega)
      have h2 : ((lenT p i T.PP : ℝ) + T.Dp + 2) * (lenT p i T.PP + T.Dp + 2 + 2 * (D.R.r : ℝ)) ≤
        ((uW p i τ a - uW p i τ b : ℤ) : ℝ) + 2 := by linarith
      exact_mod_cast h2
    · show (p.h0 : ℤ) - 1 ≤ uW p i τ a - uW p i τ b
      have := sgR_step_low D L P t a ha (by omega)
      rw [h0_eq p] at this
      have h2 : (p.h0 : ℝ) - 1 ≤ ((uW p i τ a - uW p i τ b : ℤ) : ℝ) := by linarith
      exact_mod_cast h2
    · show (p.h0 : ℤ) ≤ uW p i τ a - uW p i τ b
      have hp' : (b : ℕ) = (dat p i).p := hp
      have := sgR_step_low D L P t a (by omega) (by omega)
      rw [h0_eq p] at this
      rw [if_pos (by omega)] at hd
      have c6 : (6 : ℝ) ≤ D.R.r := by exact_mod_cast six_le_r D.R
      have h2 : (p.h0 : ℝ) ≤ ((uW p i τ a - uW p i τ b : ℤ) : ℝ) := by linarith
      exact_mod_cast h2
  · intro τ a
    obtain ⟨t, ht⟩ := exists_tau p τ
    show |(uW p i τ a : ℝ)| + ((cZeroN D ((i : ℕ) + 1) : ℤ) : ℝ) + 4 * ((dat p i).p + (dat p i).q : ℕ) ≤ 2 * (4 * L.sc.b)
    rw [uW_real p i τ t ht, eN, Int.cast_natCast]
    have a1 := hent t a (e3 ▸ a.2)
    have a2 := hent t (D.R.k - 1 - 1) (by omega)
    have a3 := abs_sub (entR D i t a) (entR D i t (D.R.k - 1 - 1))
    obtain ⟨w1, w2⟩ := hwin t
    linarith

theorem wtN : WtN := by
  refine ⟨1, one_pos, fun eps he _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun Fm _ _ _ =>
    ⟨0, le_rfl, max 8 ((3 : ℝ) ^ (4 / eps)), fun x hx hle ι p _ i => ?_⟩⟩⟩
  refine wtNum_at p i (Fm.params x hx ι) (Fm.parT x hx ι) (Fm.sizes x hx ι) ?_ ?_
  · rw [Fm.L_x x ι hx]; exact (le_max_left _ _).trans hle
  · rw [Fm.L_x x ι hx, Fm.L_eps x ι]
    have h3 : ((3 : ℝ) ^ (4 / eps)) ^ (eps / 4) = 3 := by
      rw [← Real.rpow_mul (by norm_num)]
      have : 4 / eps * (eps / 4) = 1 := by field_simp
      rw [this, Real.rpow_one]
    calc (3 : ℝ) = ((3 : ℝ) ^ (4 / eps)) ^ (eps / 4) := h3.symm
      _ ≤ x ^ (eps / 4) := Real.rpow_le_rpow (by positivity) ((le_max_right _ _).trans hle) (by positivity)

end GlobalTheory.CovTop.WtShape

end
