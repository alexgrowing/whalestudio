import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.QuoIff
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AnchoredWeightIndefiniteLiftGaps
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedWeightGapsBlockAndBar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StrictAntiOfStep
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HostBoundHolds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightBoundHolds

set_option synthInstance.maxHeartbeats 400000

noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR.Links ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop

namespace GlobalTheory.CovTop.SizeRows

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem prod_near_one {ι : Type} (s : Finset ι) (a : ι → ℝ) (e : ℝ) (n : ℕ) (he : 0 ≤ e) (hn : s.card ≤ n)
    (h : ∀ i ∈ s, 0 ≤ a i ∧ a i ≤ 1 ∧ 1 - a i ≤ e) :
    0 ≤ ∏ i ∈ s, a i ∧ ∏ i ∈ s, a i ≤ 1 ∧ 1 - ∏ i ∈ s, a i ≤ n * e := by
  classical
  refine ⟨Finset.prod_nonneg fun i hi => (h i hi).1, Finset.prod_le_one (fun i hi => (h i hi).1) fun i hi => (h i hi).2.1, ?_⟩
  refine le_trans ?_ (mul_le_mul_of_nonneg_right (Nat.cast_le.2 hn) he)
  clear hn
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.prod_insert hj, Finset.card_insert_of_notMem hj]
    have ih' := ih fun i hi => h i (Finset.mem_insert_of_mem hi)
    have hP1 : ∏ i ∈ s, a i ≤ 1 := Finset.prod_le_one (fun i hi => (h i (Finset.mem_insert_of_mem hi)).1)
      fun i hi => (h i (Finset.mem_insert_of_mem hi)).2.1
    obtain ⟨-, h1, h2⟩ := h j (Finset.mem_insert_self _ _)
    push_cast
    nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 hP1)]

theorem exists_isDiv {ι : Type} {N : ℕ} (W : GlobalTheory.MeanTop.Wts ι N) : ∃ u1, GlobalTheory.MeanTop.Wts.IsDiv { W with u1 := u1 } := by
  let U : ι → ℕ → ℤ := fun τ j => if h : j < N then W.u τ ⟨j, h⟩ else 0
  let q : ι → ℕ → ℤ := fun τ j =>
    (U τ j - U τ (j + 1) + if j + 1 = W.p then -W.c0 - (2 * (N : ℤ) - 2) else 2) / ((W.T : ℤ) + W.Dd + 1)
  refine ⟨fun τ a => ∑ j ∈ Finset.range (W.kc - 1), q τ j - ∑ j ∈ Finset.range a, q τ j, fun τ => ⟨fun a ha => ?_, fun a b hb => ?_⟩⟩
  · have : W.kc - 1 = a := by simp only at ha; omega
    simp [this]
  · have e1 : U τ a = W.u τ a := by simp [U]
    have e2 : U τ (a + 1) = W.u τ b := by rw [← hb]; simp [U]
    simp only [hb, Finset.sum_range_succ]
    rw [← e1, ← e2]
    simp only [q]
    ring

theorem rho_bounds {ι : Type} [Fintype ι] {N : ℕ} (W : GlobalTheory.MeanTop.Wts ι N) (h : W.Hyp) (hd : W.IsDiv) :
    0 ≤ GlobalTheory.CompHt.rhoOf W.u' W.u1 ∧ GlobalTheory.CompHt.rhoOf W.u' W.u1 < 1 ∧
      GlobalTheory.CompHt.rhoOf W.u' W.u1 * W.h0 ≤ 6 * Fintype.card ι * (N : ℝ) ^ 3 * W.T := by
  have hA := GlobalTheory.MeanTop.divided_strictAnti ι N W h hd
  have hG := GlobalTheory.MeanTop.divided_gaps ι N W h hd
  have hp1 := h.kc_lt
  have hp2 := h.p_lt
  have hT := h.h1
  have h0 : (0 : ℝ) < W.h0 := by
    have := h.h2.1
    have := h.weightConst_nonneg
    exact_mod_cast (by omega : 0 < W.h0)
  have he : (0 : ℝ) ≤ 6 * N * W.T / W.h0 := by positivity
  have key : ∀ τ (a l : Fin N), a < l →
      0 ≤ ((W.u' τ a : ℝ) - W.u' τ l) / ((W.u1 τ a : ℝ) - W.u1 τ l) ∧
      ((W.u' τ a : ℝ) - W.u' τ l) / ((W.u1 τ a : ℝ) - W.u1 τ l) ≤ 1 ∧
      1 - ((W.u' τ a : ℝ) - W.u' τ l) / ((W.u1 τ a : ℝ) - W.u1 τ l) ≤ 6 * N * W.T / W.h0 := by
    intro τ a l hal
    have d1 : (0 : ℝ) < (W.u1 τ a : ℝ) - W.u1 τ l := sub_pos.2 (by exact_mod_cast (hA τ).1 hal)
    have d2 : (0 : ℝ) < (W.u' τ a : ℝ) - W.u' τ l := sub_pos.2 (by exact_mod_cast (hA τ).2.1 hal)
    have hal' : (a : ℕ) < l := hal
    refine ⟨(div_pos d2 d1).le, ?_⟩
    by_cases hc : (a : ℕ) < W.p ∧ W.p ≤ l
    · have e : (W.u' τ a : ℝ) - W.u' τ l = (W.u1 τ a : ℝ) - W.u1 τ l - 3 * N := by
        simp only [GlobalTheory.MeanTop.Wts.u', if_pos hc.1, if_neg (not_lt.2 hc.2)]; push_cast; ring
      have g := ((hG τ ⟨W.p - 1, by omega⟩ ⟨W.p, hp2⟩ (by simp only; omega)).2.1 rfl).1
      have m1 := (hA τ).1.antitone (show a ≤ ⟨W.p - 1, by omega⟩ from by rw [Fin.le_def]; simp only; omega)
      have m2 := (hA τ).1.antitone (show (⟨W.p, hp2⟩ : Fin N) ≤ l from hc.2)
      have g' : W.h0 ≤ 2 * W.T * (W.u1 τ a - W.u1 τ l) :=
        g.trans (mul_le_mul_of_nonneg_left (by linarith) (by positivity))
      have g'' : (W.h0 : ℝ) ≤ 2 * W.T * ((W.u1 τ a : ℝ) - W.u1 τ l) := by exact_mod_cast g'
      have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg _
      rw [e]
      refine ⟨(div_le_one d1).2 (by linarith), ?_⟩
      rw [one_sub_div d1.ne', div_le_div_iff₀ d1 h0]
      nlinarith
    · have e : (W.u' τ a : ℝ) - W.u' τ l = (W.u1 τ a : ℝ) - W.u1 τ l := by
        simp only [GlobalTheory.MeanTop.Wts.u']
        split_ifs <;> first | (exfalso; omega) | (push_cast; ring)
      rw [e, div_self d1.ne']
      exact ⟨le_rfl, by simpa using he⟩
  have e : GlobalTheory.CompHt.rhoOf W.u' W.u1 =
      1 - ∏ τ, ∏ a, ∏ l ∈ Finset.Ioi a, ((W.u' τ a : ℝ) - W.u' τ l) / ((W.u1 τ a : ℝ) - W.u1 τ l) := by
    simp only [GlobalTheory.CompHt.rhoOf, vdm, Finset.prod_div_distrib]
    push_cast
    rfl
  have main := prod_near_one Finset.univ
    (fun τ => ∏ a, ∏ l ∈ Finset.Ioi a, ((W.u' τ a : ℝ) - W.u' τ l) / ((W.u1 τ a : ℝ) - W.u1 τ l))
    (N * (N * (6 * N * W.T / W.h0))) (Fintype.card ι) (by positivity) le_rfl fun τ _ =>
      prod_near_one Finset.univ _ (N * (6 * N * W.T / W.h0)) N (by positivity) (by simp) fun a _ =>
        prod_near_one _ _ _ N he (by simp only [Fin.card_Ioi]; omega) fun l hl => key τ a l (Finset.mem_Ioi.1 hl)
  refine ⟨by rw [e]; linarith [main.2.1], rhoOf_lt_one (fun τ => (hA τ).2.1) fun τ => (hA τ).1, ?_⟩
  rw [e, ← le_div_iff₀ h0]
  refine main.2.2.trans (le_of_eq ?_)
  ring

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m)

theorem e_pos (L : SizeData₂ D) (t : D.what₂.Tau) : 0 < (((D.hc t).e i : ℚ) : ℝ) := by
  have hx : 0 < L.sc.x := by linarith [L.sc.one_lt_alt]
  have hb : 0 < L.sc.b := Real.exp_pos _
  have hb' : 0 < L.sc.b' := by unfold Scale.b' Scale.a Scale.X'; positivity
  have hn : (0 : ℝ) < D.R.n := by exact_mod_cast (D.R.ord_pos : 0 < D.R.n)
  have hw : 0 < L.sc.w'' D.R.n := by unfold Scale.w''; positivity
  have e : wj D ((i : ℕ) + 1) t = (((D.hc t).e i : ℚ) : ℝ) := by
    unfold wj; rw [dif_pos (by simp)]; rfl
  have hi := i.2
  rw [← e]
  by_cases h1 : (D.eTau t : D.R.GG) ∈ D.host.thickPlaces
  · linarith [(L.win_thick ((i : ℕ) + 1) (by omega) (by omega) _ h1).1]
  by_cases h2 : (D.eTau t : D.R.GG) ∈ D.host.topPlaces
  · obtain ⟨s, hs, es⟩ := Finset.mem_image.mp h2
    have a1 := (L.win_top ((i : ℕ) + 1) (by omega) (by omega) t ⟨s, hs⟩ es.symm).1
    have a2 := L.bT_ge ⟨s, hs⟩
    have a3 : 0 < L.sc.b' / L.sc.x := div_pos hb' hx
    linarith
  · linarith [(L.win_thin ((i : ℕ) + 1) (by omega) (by omega) _ ⟨(D.eTau _).2, h2, h1⟩).1]

theorem exists_e_ge (L : SizeData₂ D) : ∃ t : D.what₂.Tau, L.sc.b ≤ (((D.hc t).e i : ℚ) : ℝ) := by
  classical
  have h := L.thickDensity_pos
  rw [L.typeDensity_eq_card_div] at h
  have h1 : 0 < D.host.T2.card := by
    rcases Nat.eq_zero_or_pos D.host.T2.card with h0 | h0
    · rw [h0] at h; simp at h
    · exact h0
  obtain ⟨s, hs⟩ := Finset.card_pos.1 h1
  have ht : ∃ τ : D.what₂.Tau, (D.eTau τ : D.R.GG) ∈ D.host.thickPlaces := by
    refine ⟨D.eTau.symm ⟨D.R.tau2 (D.R.dig s + D.host.u0), rfl⟩, ?_⟩
    rw [Equiv.apply_symm_apply]
    unfold Formalism.BasicNotions.Host.thickPlaces
    exact Finset.mem_image.2 ⟨s, hs, rfl⟩
  obtain ⟨t, ht⟩ := ht
  have e : wj D ((i : ℕ) + 1) t = (((D.hc t).e i : ℚ) : ℝ) := by
    unfold wj; rw [dif_pos (by simp)]; rfl
  have hi := i.2
  exact ⟨t, e ▸ (L.win_thick ((i : ℕ) + 1) (by omega) (by omega) _ ht).1⟩

theorem e_le_row (hp : (dat p i).p = (D.R.sigW ((i : ℕ) + 1)).1) (τ : Psi p.T.Q.H) (t : D.what₂.Tau)
    (ht : τ.1 = DV.tauEmb D t) :
    (((D.hc t).e i : ℚ) : ℝ) ≤ ∑ k, |(laOf (dat p i) (wtA (p.κ i)) (p.κ i).n τ k : ℝ)| + D.R.r := by
  have hk := D.R.m_add_three_le_k
  have hm := D.R.two_le_m
  have hi := i.2
  have hr : D.R.r = D.R.k + D.R.m - 1 := rfl
  have hs : (D.R.sigW ((i : ℕ) + 1)).1 = D.R.k + (i : ℕ) := by simp only [Ranks.sigW]; omega
  have h0 : 0 < (D.R.sigW ((i : ℕ) + 1)).1 := by omega
  have hn := (p.fw.kap i t).2.2
  let k0 : Fin ((dat p i).p + (dat p i).q) := ⟨0, by omega⟩
  have e1 : laOf (dat p i) (wtA (p.κ i)) (p.κ i).n τ k0 =
      (aPl D i (D.R.sigW ((i : ℕ) + 1)).1 t 0 : ℤ) + ((D.R.nV / 2 : ℕ) : ℤ) := by
    simp only [laOf, weightOf, k0]
    rw [if_pos (by omega), ht, hn, GlobalTheory.Shares.WtDic.wtA_tau]
    unfold ext0
    rw [dif_pos h0, (p.fw.kap i t).1 ⟨0, h0⟩, GlobalTheory.RecGaps.sig_Wc]
  have e2 := Finset.single_le_sum (f := fun k => |(laOf (dat p i) (wtA (p.κ i)) (p.κ i).n τ k : ℝ)|)
    (fun k _ => abs_nonneg _) (Finset.mem_univ k0)
  have e3 := le_abs_self (laOf (dat p i) (wtA (p.κ i)) (p.κ i).n τ k0 : ℝ)
  have e4 : Formalism.L2.NTheta.lamAt (D.hc t) 0 = (D.hc t).v ⟨0, by omega⟩ := by
    unfold Formalism.L2.NTheta.lamAt; rw [dif_pos (by omega)]
  have e5 := (L.cloud_v t ⟨0, by omega⟩).1
  have e6 : ∀ y : ℚ, (y : ℝ) - 1 ≤ ((⌊y⌋.toNat : ℕ) : ℝ) := fun y => by
    have a1 : ((y - 1 : ℚ) : ℝ) < ((⌊y⌋ : ℚ) : ℝ) := by exact_mod_cast Int.sub_one_lt_floor y
    have a2 : ((⌊y⌋ : ℤ) : ℝ) ≤ ((⌊y⌋.toNat : ℕ) : ℝ) := by exact_mod_cast Int.self_le_toNat ⌊y⌋
    push_cast at a1
    linarith
  have e7 : (((D.hc t).v ⟨0, by omega⟩ : ℚ) : ℝ) + (((D.hc t).e i : ℚ) : ℝ) - (((D.R.sigW ((i : ℕ) + 1)).1 : ℝ) - 1) -
      ((D.R.t : ℝ) + 1) / 2 - 1 ≤ (aPl D i (D.R.sigW ((i : ℕ) + 1)).1 t 0 : ℝ) := by
    unfold aPl
    rw [if_pos h0, e4]
    refine le_trans (le_of_eq ?_) (e6 _)
    push_cast; ring
  have e8 : ((D.R.r : ℝ) + D.R.t - 1) ≤ 2 * ((D.R.nV / 2 : ℕ) : ℝ) := by
    have : D.R.r + D.R.t ≤ 2 * (D.R.nV / 2) + 1 := by unfold Ranks.nV; omega
    have : (D.R.r : ℝ) + D.R.t ≤ 2 * ((D.R.nV / 2 : ℕ) : ℝ) + 1 := by exact_mod_cast this
    linarith
  have e9 : ((D.R.sigW ((i : ℕ) + 1)).1 : ℝ) ≤ D.R.r := by exact_mod_cast (by omega : (D.R.sigW ((i : ℕ) + 1)).1 ≤ D.R.r)
  have e10 : (2 : ℝ) ≤ D.R.r := by exact_mod_cast (by omega : 2 ≤ D.R.r)
  have e11 : (laOf (dat p i) (wtA (p.κ i)) (p.κ i).n τ k0 : ℝ) =
      (aPl D i (D.R.sigW ((i : ℕ) + 1)).1 t 0 : ℝ) + ((D.R.nV / 2 : ℕ) : ℝ) := by
    rw [e1, Int.cast_add, Int.cast_natCast, Int.cast_natCast]
  linarith

theorem sum_e_le (hp : (dat p i).p = (D.R.sigW ((i : ℕ) + 1)).1) (hc : Nat.card (Psi p.T.Q.H) = D.R.f) :
    ∑ ρ : RPl D.R, (((D.hc (tauPl D ρ)).e i : ℚ) : ℝ) ≤ kap p i + D.R.f * D.R.r ∧ L.sc.b ≤ kap p i + D.R.r := by
  have hQ : p.T.Q.Pins := p.fw.laws.pins
  have hb := tauPl_bijective D
  have ex : ∀ τ : Psi p.T.Q.H, ∃ ρ : RPl D.R, τ.1 = DV.tauEmb D (tauPl D ρ) := fun τ => by
    obtain ⟨t, ht⟩ := ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.exists_tau_of_inPsi p.T.Q hQ.1 τ.1 τ.2
    obtain ⟨ρ, rfl⟩ := hb.2 t
    exact ⟨ρ, ht⟩
  choose g hg using ex
  have hinj : Function.Injective g := fun a b hab => Subtype.ext (by rw [hg a, hg b, hab])
  have hcard : Fintype.card (Psi p.T.Q.H) = D.R.f := by rw [← hc, Nat.card_eq_fintype_card]
  have hbij : Function.Bijective g := (Fintype.bijective_iff_injective_and_card g).2
    ⟨hinj, by rw [hcard]; simp [Ranks.f, Ranks.n, D.R.card_A]⟩
  constructor
  · rw [← hbij.sum_comp]
    refine (Finset.sum_le_sum fun τ _ => e_le_row p i hp τ _ (hg τ)).trans (le_of_eq ?_)
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, hcard, nsmul_eq_mul]
    rfl
  · obtain ⟨t, ht⟩ := exists_e_ge i L
    obtain ⟨ρ, rfl⟩ := hb.2 t
    obtain ⟨τ, rfl⟩ := hbij.2 ρ
    have a1 := e_le_row p i hp τ _ (hg τ)
    have a2 := Finset.single_le_sum (f := fun τ => ∑ k, |(laOf (dat p i) (wtA (p.κ i)) (p.κ i).n τ k : ℝ)|)
      (fun τ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ τ)
    have a3 : kap p i = ∑ τ, ∑ k, |(laOf (dat p i) (wtA (p.κ i)) (p.κ i).n τ k : ℝ)| := rfl
    linarith

theorem mainT_le (hom : |(ofRecord D L p.Del p.h0).logOm| ≤ 3 * L.sc.L) :
    |mainT p i| ≤ 3 * D.R.r * L.sc.L * ∑ ρ : RPl D.R, (((D.hc (tauPl D ρ)).e i : ℚ) : ℝ) := by
  have e : mainT p i = ∑ ρ : RPl D.R, (((D.R.k : ℝ) + (((i : ℕ) + 1 : ℕ) : ℝ) - 1) - ((D.R.m : ℝ) - (((i : ℕ) + 1 : ℕ) : ℝ))) *
    (ofRecord D L p.Del p.h0).w ((i : ℕ) + 1) ρ * (ofRecord D L p.Del p.h0).logOm := rfl
  have hi := i.2
  have hk := D.R.m_add_three_le_k
  have hw : ∀ ρ : RPl D.R, (ofRecord D L p.Del p.h0).w ((i : ℕ) + 1) ρ = (((D.hc (tauPl D ρ)).e i : ℚ) : ℝ) := fun ρ => by
    unfold NumDatum.w NumDatum.eQ
    rw [dif_pos ⟨by omega, hi⟩]; rfl
  have hr : (D.R.r : ℝ) + 1 = D.R.k + D.R.m := by exact_mod_cast (by unfold Ranks.r; omega : D.R.r + 1 = D.R.k + D.R.m)
  have h1 : (((i : ℕ) + 1 : ℕ) : ℝ) ≤ D.R.m := by exact_mod_cast hi
  have h2 : (1 : ℝ) ≤ (((i : ℕ) + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ (i : ℕ) + 1)
  have h3 : (0 : ℝ) ≤ D.R.k := Nat.cast_nonneg _
  have hc : |((D.R.k : ℝ) + (((i : ℕ) + 1 : ℕ) : ℝ) - 1) - ((D.R.m : ℝ) - (((i : ℕ) + 1 : ℕ) : ℝ))| ≤ D.R.r :=
    abs_le.2 ⟨by linarith, by linarith⟩
  rw [e, Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun ρ _ => ?_)
  have h0 := (e_pos i L (tauPl D ρ)).le
  rw [hw, abs_mul, abs_mul, abs_of_nonneg h0]
  refine (mul_le_mul (mul_le_mul_of_nonneg_right hc h0) hom (abs_nonneg _) (by positivity)).trans (le_of_eq ?_)
  ring

theorem numbers {f r l PP b : ℝ} (hf : 8 ≤ f) (hr : 2 ≤ r) (hl : 10 ≤ l) (hP : (f * r * l) ^ 12 ≤ PP) (hb : f * r * r * l ≤ b) :
    6400 * r ^ 2 ≤ PP ∧ 9 * (r * l) ≤ PP ∧ 100 ≤ PP ∧ 100 ≤ PP ^ 2 ∧ 16 ≤ f * r ∧ f * r * 20 ≤ b ∧ r ≤ f * r := by
  have h0 : 0 ≤ r * l := by positivity
  have h1 : 8 * (r * l) ≤ f * r * l := by nlinarith
  have h2 : 10 * r ≤ r * l := by nlinarith
  have h3 : (f * r * l) ^ 2 ≤ PP := (pow_le_pow_right₀ (by linarith) (by norm_num)).trans hP
  have h4 : 16 ≤ f * r := by nlinarith
  have h5 : f * r * 20 ≤ f * r * (r * l) := mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  have h6 : r ≤ f * r := by nlinarith
  generalize f * r * l = Z at *
  have h7 : 160 * Z ≤ Z ^ 2 := by nlinarith
  have h8 : (80 * r) ^ 2 ≤ Z ^ 2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
  have h9 : 100 ≤ PP := by linarith
  exact ⟨by linarith, by linarith, h9, by nlinarith, h4, by linarith, h6⟩

theorem sizeAt_of {PP A : ℝ} (hH : HostNum D L PP A 1) (hW : WtNum p i PP) : SizeAt p i PP (A + 2) := by
  obtain ⟨-, hL, hLx, hll⟩ := hH.big
  obtain ⟨hA, -, hpoly⟩ := hH.poly
  have hroom : L.sc.x ^ A ≤ L.sc.b := by simpa using hH.room
  have hk := D.R.m_add_three_le_k
  have hm := D.R.two_le_m
  have hrn : D.R.r = D.R.k + D.R.m - 1 := rfl
  have hf : (8 : ℝ) ≤ D.R.f := by exact_mod_cast hH.f8
  have hm' : (2 : ℝ) ≤ D.R.m := by exact_mod_cast hm
  have hmk : (D.R.m : ℝ) ≤ D.R.k := by exact_mod_cast (by omega : D.R.m ≤ D.R.k)
  have hmr : (D.R.m : ℝ) ≤ D.R.r := by exact_mod_cast (by omega : D.R.m ≤ D.R.r)
  have hrV : (D.R.r : ℝ) ≤ D.R.nV := by exact_mod_cast (by unfold Ranks.nV; omega : D.R.r ≤ D.R.nV)
  have hx : 10 ≤ L.sc.x := hL.trans hLx
  have hx2 : L.sc.x ^ (A + 2) = L.sc.x ^ A * L.sc.x ^ 2 := by
    rw [Real.rpow_add (by linarith), Real.rpow_two]
  have hllx : Real.log (Real.log L.sc.x) ≤ L.sc.x := by
    have a0 : 0 < Real.log L.sc.x := Real.log_pos (by linarith)
    linarith [Real.log_le_sub_one_of_pos a0, Real.log_le_sub_one_of_pos (by linarith : 0 < L.sc.x)]
  obtain ⟨hs1, hs2⟩ := sum_e_le p i hW.sig.1 hW.card
  have hmain := mainT_le p i hW.om
  have hcard : Fintype.card (Psi p.T.Q.H) = D.R.f := by rw [← hW.card, Nat.card_eq_fintype_card]
  have hkap : kap p i ≤ D.R.f * (D.R.r * (4 * L.sc.b)) := by
    refine (Finset.sum_le_sum fun τ _ => Finset.sum_le_sum fun k _ => hW.up τ k).trans (le_of_eq ?_)
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, hcard, hW.sig.2.2, nsmul_eq_mul]
  have hfr : (D.R.f : ℝ) * D.R.r * D.R.r * L.sc.L ≤ L.sc.x ^ A :=
    le_trans (by gcongr) hpoly
  obtain ⟨hPr, hPL, hP100, hP2, hfr0, hfr1, hrf⟩ := numbers hf (hm'.trans hmr) hL hH.ppLow (hfr.trans hroom)
  have hxx : L.sc.x ≤ L.sc.x ^ 2 ∧ 36 ≤ L.sc.x ^ 2 := by
    have := mul_le_mul_of_nonneg_left hx (by linarith : 0 ≤ L.sc.x)
    rw [sq]; constructor <;> linarith
  have hb1 : 1 ≤ L.sc.b := by linarith
  have hbk : L.sc.b ≤ 2 * kap p i := by linarith
  have hk0 : 0 ≤ kap p i := by linarith
  have hm9 : |mainT p i| ≤ 9 * (D.R.r * L.sc.L) * kap p i := by
    refine hmain.trans ?_
    have := mul_le_mul_of_nonneg_left (show ∑ ρ : RPl D.R, (((D.hc (tauPl D ρ)).e i : ℚ) : ℝ) ≤ 3 * kap p i by linarith)
      (show 0 ≤ 3 * (D.R.r : ℝ) * L.sc.L by positivity)
    linarith
  have hX0 : 0 ≤ L.sc.x ^ A := by positivity
  refine ⟨hb1, ?_, ?_, ?_, hm9.trans (mul_le_mul_of_nonneg_right hPL hk0),
    hbk.trans (mul_le_mul_of_nonneg_right (by linarith) hk0), fun hi => ?_⟩
  · rw [hW.unit]
    calc L.sc.b = 1 * 1 * L.sc.b * 1 * 1 := by ring
      _ ≤ _ := by gcongr <;> linarith
  · rw [hW.unit, hx2]
    have a1 : (D.R.f : ℝ) * D.R.m * L.sc.L ≤ L.sc.x ^ A := by
      refine le_trans ?_ hfr
      calc (D.R.f : ℝ) * D.R.m * L.sc.L = D.R.f * D.R.m * 1 * L.sc.L := by ring
        _ ≤ _ := by gcongr; linarith
    calc _ = (D.R.f : ℝ) * D.R.m * L.sc.L * Real.log (Real.log L.sc.x) * L.sc.b := by ring
      _ ≤ _ := by gcongr; exact hllx.trans hxx.1
  · rw [hx2]
    calc _ ≤ 9 * (D.R.r * L.sc.L) * (D.R.f * (D.R.r * (4 * L.sc.b))) :=
          hm9.trans (mul_le_mul_of_nonneg_left hkap (by positivity))
      _ = (D.R.f : ℝ) * D.R.r * D.R.r * L.sc.L * 36 * L.sc.b := by ring
      _ ≤ _ := by gcongr; exact hxx.2
  · obtain ⟨h0, S, eta, -, -, -, -, hh0, hyp⟩ := hW.hyp hi
    refine ⟨exists_isDiv (wtsAt p i PP h0 S eta 0), fun u1 hu => ?_⟩
    obtain ⟨r0, r1, r2⟩ := rho_bounds _ (hyp u1) ((quo_iff p i PP h0 S eta u1).1 hu)
    have er : GlobalTheory.CompHt.rhoOf (wtsAt p i PP h0 S eta u1).u' (wtsAt p i PP h0 S eta u1).u1 = rhoB (dat p i) u1 := by
      unfold rhoB
      congr 1
      funext τ k
      rw [uPrime_apply]; rfl
    rw [er] at r0 r1 r2
    have hT : 4 * dimFlag (dat p i) + 4 ≤ lenT p i PP := (hyp u1).h1
    have hD : 1 ≤ dimFlag (dat p i) := by
      rw [hW.dim]
      exact Nat.mul_pos (by have := hH.f8; omega) (Nat.choose_pos (by omega))
    refine ⟨by omega, r0, r1, ?_⟩
    have r3 : rhoB (dat p i) u1 * h0 ≤ 6 * D.R.f * (D.R.r : ℝ) ^ 3 * lenT p i PP := by
      rw [← hcard, ← hW.sig.2.2]; exact r2
    have hT0 : (0 : ℝ) < lenT p i PP := by exact_mod_cast (by omega : 0 < lenT p i PP)
    have hD0 : (0 : ℝ) < dimFlag (dat p i) := by exact_mod_cast hD
    have hTl : PP ^ 2 * (dimFlag (dat p i) : ℝ) ^ 2 ≤ lenT p i PP := by
      refine le_trans ?_ (Nat.le_ceil _)
      rw [le_div_iff₀ (by linarith)]
      gcongr
    unfold zed
    generalize (lenT p i PP : ℝ) = T at *
    generalize (dimFlag (dat p i) : ℝ) = d at *
    generalize rhoB (dat p i) u1 = ρ at *
    have z1 : d ^ 2 / T ≤ 1 / 100 := by
      rw [div_le_div_iff₀ hT0 (by norm_num)]
      have : 100 * d ^ 2 ≤ PP ^ 2 * d ^ 2 := by gcongr
      linarith
    have hr0 : (0 : ℝ) < D.R.r := by linarith
    have z2 : 6400 * (D.R.r : ℝ) ^ 2 * T * D.R.r * (D.R.f * 1) * 1 * 1 * d ≤ h0 := by
      refine le_trans ?_ hh0
      rw [sq (D.R.f : ℝ)]
      have : (1 : ℝ) ≤ (D.R.m : ℝ) ^ 2 := one_le_pow₀ (by linarith)
      gcongr <;> linarith
    have z3 : ρ * (6400 * (D.R.r : ℝ) ^ 2 * T * D.R.r * (D.R.f * 1) * 1 * 1 * d) ≤ 6 * D.R.f * (D.R.r : ℝ) ^ 3 * T :=
      (mul_le_mul_of_nonneg_left z2 r0).trans r3
    have z4 : 6400 * (d * ρ) ≤ 6 := by
      have hpos : (0 : ℝ) < D.R.f * (D.R.r : ℝ) ^ 3 * T := by positivity
      refine le_of_mul_le_mul_right ?_ hpos
      linarith
    linarith

theorem size_of (h1 : HostN 1) (h2 : WtN) : Size := by
  refine (Closed.and h1 h2).imp fun Fm CH _ h => ?_
  obtain ⟨⟨A, hA, hH⟩, _, _, hW⟩ := h
  refine ⟨A + 2, by linarith, ?_⟩
  obtain ⟨x0, h⟩ := hH.and hW
  exact ⟨x0, fun x hx hle ι p hp i => sizeAt_of p i ((h x hx hle ι p hp).1 i) ((h x hx hle ι p hp).2 i)⟩

theorem size : Size := size_of (GlobalTheory.CovTop.Sizes.hostN 1) GlobalTheory.CovTop.WtShape.wtN

end GlobalTheory.CovTop.SizeRows

end
