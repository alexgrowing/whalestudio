import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasAtOf
import Development.AbelianVarietyTheory.Definitions.Divisors.QuoIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HostBoundHolds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightBoundHolds
import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.CovTop.MeasRd
open Formalism.MainNotions

set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.CovTop.MeasUp

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem le_exp_of_log_le {y L : ℝ} (hy : 0 ≤ y) (h : Real.log y ≤ L) : y ≤ Real.exp L := by
  rcases hy.eq_or_lt with h0 | h0
  · rw [← h0]; exact (Real.exp_pos L).le
  · exact (Real.log_le_iff_le_exp h0).1 h

theorem kapQ_inl (D : D7) (i : Fin D.R.m) (t : D.what₂.Tau) {p q : ℕ} (hp : p = D.R.k + i)
    (hq : q = D.R.m - ((i : ℕ) + 1)) (a : Fin p) :
    Formalism.L2.NTheta.kapQ (D.hc t) p q (Sum.inl a) + (D.hc t).e i = GlobalTheory.CovTop.WtShape.ent D i t a := by
  have hk := D.R.m_add_three_le_k
  have hm := D.R.two_le_m
  have hi := i.2
  have ha := a.2
  have e0 : Formalism.L2.NTheta.lamAt (D.hc t) a = DV.sigPar D t a := rfl
  unfold Formalism.L2.NTheta.kapQ GlobalTheory.CovTop.WtShape.ent
  simp only [Sum.elim_inl]
  rw [if_pos (by omega), e0]
  subst hp hq
  have hr : D.R.r = D.R.k + D.R.m - 1 := rfl
  rw [hr, Nat.cast_sub (by omega : 1 ≤ D.R.k + D.R.m), Nat.cast_sub (by omega : (i : ℕ) + 1 ≤ D.R.m)]
  push_cast
  ring

theorem kapQ_inr (D : D7) (i : Fin D.R.m) (t : D.what₂.Tau) {p q : ℕ} (hp : p = D.R.k + i)
    (hq : q = D.R.m - ((i : ℕ) + 1)) (c : Fin q) :
    Formalism.L2.NTheta.kapQ (D.hc t) p q (Sum.inr c) + (D.hc t).e i = GlobalTheory.CovTop.WtShape.ent D i t (p + c) := by
  have hk := D.R.m_add_three_le_k
  have hm := D.R.two_le_m
  have hi := i.2
  have hc := c.2
  have e0 : Formalism.L2.NTheta.lamAt (D.hc t) (p + c) = DV.sigPar D t (p + c) := rfl
  unfold Formalism.L2.NTheta.kapQ GlobalTheory.CovTop.WtShape.ent
  simp only [Sum.elim_inr]
  rw [if_neg (by omega), e0]
  subst hp hq
  have hr : D.R.r = D.R.k + D.R.m - 1 := rfl
  rw [hr, Nat.cast_sub (by omega : 1 ≤ D.R.k + D.R.m), Nat.cast_sub (by omega : (i : ℕ) + 1 ≤ D.R.m)]
  push_cast
  ring

theorem abs_wt_le (D : D7) (i : Fin D.R.m) (t : D.what₂.Tau) {p q : ℕ} (hp : p = D.R.k + i)
    (hq : q = D.R.m - ((i : ℕ) + 1)) {B : ℝ}
    (hB : ∀ n, n < D.R.r → |((GlobalTheory.CovTop.WtShape.ent D i t n : ℚ) : ℝ)| ≤ B) (a : Fin p ⊕ Fin q) :
    |((Formalism.L2.NTheta.kapW (D.hc t) p q a : ℤ) : ℝ) + (((D.hc t).e i : ℚ) : ℝ)| ≤ B + 1 := by
  have hk := D.R.m_add_three_le_k
  have hm := D.R.two_le_m
  have hi := i.2
  have hr : D.R.r = D.R.k + D.R.m - 1 := rfl
  obtain ⟨n, hn, hx⟩ : ∃ n, n < D.R.r ∧
      Formalism.L2.NTheta.kapQ (D.hc t) p q a + (D.hc t).e i = GlobalTheory.CovTop.WtShape.ent D i t n := by
    cases a with
    | inl a => exact ⟨a, by have := a.2; omega, kapQ_inl D i t hp hq a⟩
    | inr c => exact ⟨p + c, by have := c.2; omega, kapQ_inr D i t hp hq c⟩
  have h1 : ((Formalism.L2.NTheta.kapW (D.hc t) p q a : ℤ) : ℝ) ≤ (Formalism.L2.NTheta.kapQ (D.hc t) p q a : ℝ) := by
    unfold Formalism.L2.NTheta.kapW
    exact_mod_cast Int.floor_le _
  have h2 : (Formalism.L2.NTheta.kapQ (D.hc t) p q a : ℝ) < ((Formalism.L2.NTheta.kapW (D.hc t) p q a : ℤ) : ℝ) + 1 := by
    have h := Int.lt_floor_add_one (Formalism.L2.NTheta.kapQ (D.hc t) p q a)
    have h' : ((Formalism.L2.NTheta.kapQ (D.hc t) p q a : ℚ) : ℝ) <
        (((⌊Formalism.L2.NTheta.kapQ (D.hc t) p q a⌋ : ℤ) : ℚ) : ℝ) + 1 := by
      have := (Rat.cast_lt (K := ℝ)).2 h
      rw [Rat.cast_add, Rat.cast_one] at this
      exact this
    rw [Rat.cast_intCast] at h'
    exact h'
  have h3 : (Formalism.L2.NTheta.kapQ (D.hc t) p q a : ℝ) + (((D.hc t).e i : ℚ) : ℝ) =
      ((GlobalTheory.CovTop.WtShape.ent D i t n : ℚ) : ℝ) := by
    rw [← hx]; push_cast; ring
  obtain ⟨b1, b2⟩ := abs_le.1 (hB n hn)
  rw [abs_le]
  constructor <;> linarith

theorem wtSize_le (D : D7) (i : Fin D.R.m) {B : ℝ}
    (hB : ∀ t n, n < D.R.r → |((GlobalTheory.CovTop.WtShape.ent D i t n : ℚ) : ℝ)| ≤ B) :
    GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.wtSize D i ≤ D.R.f * D.R.r * (B + 1) := by
  have hk := D.R.m_add_three_le_k
  have hm := D.R.two_le_m
  have hi := i.2
  have hr : D.R.r = D.R.k + D.R.m - 1 := rfl
  unfold GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.wtSize
  calc _ ≤ ∑ _τ : D.what₂.Tau, (D.R.r : ℝ) * (B + 1) := Finset.sum_le_sum fun τ _ => ?_
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, D.what₂.card_Tau, nsmul_eq_mul]; ring
  have hs : (Wc D i).sig (TH.tauE D τ) = D.R.sigW ((i : ℕ) + 1) := D.sp.W_sigval _ (Nat.le_add_left _ _) i.2 _
  have s1 : ((Wc D i).sig (TH.tauE D τ)).1 = D.R.k + i := by rw [hs]; rfl
  have s2 : ((Wc D i).sig (TH.tauE D τ)).2 = D.R.m - ((i : ℕ) + 1) := by rw [hs]; rfl
  calc _ ≤ ∑ _a : Fin ((Wc D i).sig (TH.tauE D τ)).1 ⊕ Fin ((Wc D i).sig (TH.tauE D τ)).2, (B + 1) :=
        Finset.sum_le_sum fun a _ => abs_wt_le D i τ s1 s2 (hB τ) a
    _ = _ := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_sum, Fintype.card_fin, Fintype.card_fin, nsmul_eq_mul, s1, s2]
      congr 1
      rw [hr]; push_cast [show (i : ℕ) + 1 ≤ D.R.m by omega, show 1 ≤ D.R.k + D.R.m by omega]; ring

end GlobalTheory.CovTop.MeasUp

namespace GlobalTheory.CovTop.MeasUp

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m)

theorem abs_ent_le {PP : ℝ} (hW : WtNum p i PP) (t : D.what₂.Tau) (n : ℕ) (hn : n < D.R.r) :
    |((GlobalTheory.CovTop.WtShape.ent D i t n : ℚ) : ℝ)| ≤ 4 * L.sc.b := by
  have hp := p.fw.laws.pins.1
  let τ : Psi p.T.Q.H := ⟨DV.tauEmb D t, hp.2.2.2 t⟩
  let k : Fin ((dat p i).p + (dat p i).q) := ⟨n, by rw [GlobalTheory.CovTop.WtShape.dat_rank p i]; exact hn⟩
  have e := GlobalTheory.CovTop.WtShape.laOf_read p i τ t rfl k
  have h := hW.up τ k
  rw [← e, Rat.cast_intCast]
  exact h

theorem sizes_two {PP A PP' : ℝ} (P : ParameterChoice' D L) (hH : HostNum D L PP A 2) (hW : ∀ j, WtNum p j PP') :
    GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.Sizes D (2 * L.sc.L) := by
  have hk := D.R.m_add_three_le_k
  have hm := D.R.two_le_m
  have hr1 : 1 ≤ D.R.r := by unfold Ranks.r; omega
  have hrR : (1 : ℝ) ≤ D.R.r := by exact_mod_cast hr1
  have hf8 : (8 : ℝ) ≤ D.R.f := by exact_mod_cast hH.f8
  have hnV : (0 : ℝ) ≤ D.R.nV := Nat.cast_nonneg _
  obtain ⟨hL10, -⟩ := hH.big.2
  obtain ⟨hlfr, hlnV⟩ := hH.logfr
  set Lc := L.sc.L with hLc
  have hb : L.sc.b = Real.exp Lc := rfl
  have hfr : (D.R.f : ℝ) * D.R.r ≤ Real.exp Lc := le_exp_of_log_le (by positivity) hlfr
  have hnVe : (D.R.nV : ℝ) ≤ Real.exp Lc := le_exp_of_log_le hnV hlnV
  have hE0 : 0 < Real.exp Lc := Real.exp_pos _
  have hE1 : Lc + 1 ≤ Real.exp Lc := Real.add_one_le_exp _
  have e2 : Real.exp (2 * Lc) = Real.exp Lc * Real.exp Lc := by rw [two_mul, Real.exp_add]
  refine ⟨?_, fun j => ?_, ?_, ?_⟩
  · rw [e2]
    exact mul_le_mul hfr hnVe hnV hE0.le
  · have hw := wtSize_le D j (abs_ent_le p j (hW j))
    rw [e2, ← hb]
    rw [← hb] at hE1 hfr
    have h1 : (D.R.f : ℝ) * D.R.r * (4 * L.sc.b + 1) ≤ L.sc.b * (5 * L.sc.b) :=
      mul_le_mul hfr (by linarith) (by linarith) (by linarith)
    have h5 : 5 ≤ L.sc.b * L.sc.b := by nlinarith
    have h6 : L.sc.b * (5 * L.sc.b) ≤ (L.sc.b * L.sc.b) ^ 2 := by nlinarith
    linarith
  · have g0 : (0 : ℝ) < (D.host.g 0 : ℝ) := by exact_mod_cast (D.host.g_prime 0).pos
    have g1 : (0 : ℝ) < (D.host.g 1 : ℝ) := by exact_mod_cast (D.host.g_prime 1).pos
    rw [Real.log_mul g0.ne' g1.ne']
    linarith [hH.logg 0, hH.logg 1]
  · have h1 := Formalism.BasicNotions.log_rdE_le_scL P
    have h2 : |dlogL D 1| ≤ Lc := by
      rw [← L.logDerivative_at_one_eq]; exact P.logDerivative_le_power
    linarith

theorem ratAt_pos_le (hOM : ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.OneMeasure D) {PP A PP' : ℝ} (P : ParameterChoice' D L)
    (hH : HostNum D L PP A 2) (hW : ∀ j, WtNum p j PP') :
    0 < ratAt p i ∧ Real.log (ratAt p i) ≤ 244 * unitE p := by
  obtain ⟨-, hd, h2⟩ := hOM D _ p.R.toLevCh _ p.charW.base.lev i p.R.triv
  obtain ⟨h0, ht, -, hb⟩ := h2 _ _ (p.charW.base.models.νW i)
  have hr : 0 < ratAt p i :=
    mul_pos (ENNReal.toReal_pos h0 ht) (Finset.prod_pos fun τ _ => zero_lt_one.trans_le (hd τ))
  refine ⟨hr, ?_⟩
  have hB := (hb _ (sizes_two p P hH hW)).2.2
  have hk := D.R.m_add_three_le_k
  have hm := D.R.two_le_m
  have hr1 : 1 ≤ D.R.r := by unfold Ranks.r; omega
  have hrR : (1 : ℝ) ≤ D.R.r := by exact_mod_cast hr1
  have hf8 : (8 : ℝ) ≤ D.R.f := by exact_mod_cast hH.f8
  have hmR : (2 : ℝ) ≤ D.R.m := by exact_mod_cast hm
  have hnV1 : (1 : ℝ) ≤ D.R.nV := by
    have : 1 ≤ D.R.nV := by unfold Ranks.nV; omega
    exact_mod_cast this
  obtain ⟨-, hL10, -, hll⟩ := hH.big
  obtain ⟨-, -, hpoly⟩ := hH.poly
  have hroom := hH.room
  rw [Real.rpow_two] at hroom

  have hr_le : (D.R.r : ℝ) ≤ L.sc.x ^ A := by
    refine le_trans ?_ hpoly
    have a1 : (D.R.r : ℝ) ≤ (D.R.f : ℝ) * D.R.r := le_mul_of_one_le_left (by linarith) (by linarith)
    have a2 : (D.R.f : ℝ) * D.R.r ≤ (D.R.f : ℝ) * D.R.r * D.R.nV := le_mul_of_one_le_right (by positivity) hnV1
    have a3 : (D.R.f : ℝ) * D.R.r * D.R.nV ≤ (D.R.f : ℝ) * D.R.r * D.R.nV * L.sc.L :=
      le_mul_of_one_le_right (by positivity) (by linarith)
    linarith
  have hr2 : (D.R.r : ℝ) ^ 2 ≤ L.sc.b := (pow_le_pow_left₀ (by linarith) hr_le 2).trans hroom
  have hu : unitE p = (D.R.f : ℝ) * D.R.m * L.sc.b * L.sc.L * Real.log (Real.log L.sc.x) := (hW i).unit
  rw [hu]
  have hL0 : 0 ≤ L.sc.L := by linarith
  have hfL : 0 ≤ (D.R.f : ℝ) * L.sc.L := by positivity
  have c1 : (D.R.f : ℝ) * (D.R.r : ℝ) ^ 2 * L.sc.L ≤ (D.R.f : ℝ) * L.sc.b * L.sc.L := by
    have := mul_le_mul_of_nonneg_left hr2 hfL
    nlinarith
  have hb1 : 0 ≤ (D.R.f : ℝ) * L.sc.b * L.sc.L := by
    have : 0 < L.sc.b := Real.exp_pos _
    positivity
  have c2 : (D.R.f : ℝ) * L.sc.b * L.sc.L ≤ (D.R.f : ℝ) * D.R.m * L.sc.b * L.sc.L * Real.log (Real.log L.sc.x) := by
    have h1 : (1 : ℝ) ≤ D.R.m * Real.log (Real.log L.sc.x) := by nlinarith
    have := mul_le_mul_of_nonneg_left h1 hb1
    nlinarith
  have e3 : (122 : ℝ) * ((D.R.f : ℝ) * (D.R.r : ℝ) ^ 2 * (2 * L.sc.L)) = 244 * ((D.R.f : ℝ) * (D.R.r : ℝ) ^ 2 * L.sc.L) := by
    ring
  have e4 : ratAt p i = GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.ratio D i (p.R.νW i) (p.R.fdW i) := rfl
  rw [e4]
  linarith

end GlobalTheory.CovTop.MeasUp

namespace GlobalTheory.CovTop.MeasRd

theorem ratAt_upper : (∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.OneMeasure D) → Closed FamHyp fun Fm _ =>
    ∃ K : ℝ, 0 ≤ K ∧ EvTied Fm fun _ _ _ p => ∀ i, 0 < ratAt p i ∧ Real.log (ratAt p i) ≤ K * unitE p := by
  intro hOM
  refine Closed.imp (Closed.and (GlobalTheory.CovTop.Sizes.hostN 2) GlobalTheory.CovTop.WtShape.wtN) fun Fm CH _ h => ?_
  obtain ⟨⟨A, -, hA⟩, ⟨C, -, hC⟩⟩ := h
  obtain ⟨x0, hx⟩ := EvTied.and hA hC
  refine ⟨244, by norm_num, x0, fun x hx' hle ι p hp i => ?_⟩
  obtain ⟨h1, h2⟩ := hx x hx' hle ι p hp
  exact GlobalTheory.CovTop.MeasUp.ratAt_pos_le p i hOM (Fm.params x hx' ι) (h1 i) h2

end GlobalTheory.CovTop.MeasRd

end
