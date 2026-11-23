import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.QuoIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HostBoundHolds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightBoundHolds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjCmHostRootNeSelf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AnchoredWeightIndefiniteLiftGaps

set_option synthInstance.maxHeartbeats 400000

noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CovTop.AnchorRd

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m)

theorem anchor_eq (P : ParameterChoice' D L) (t : D.what₂.Tau) (τ : Psi p.T.Q.H) (hτ : τ.1 = DV.tauEmb D t) :
    (anchor (dat p i) (wtA (p.κ i)) (p.κ i).n (D.R.k - 1) τ : ℤ) =
      ⌊Formalism.L2.NTheta.lamAt (D.hc t) (D.R.k - 2) + (D.hc t).e i -
        (((D.R.sigW ((i : ℕ) + 1)).1 : ℚ) - ((D.R.k - 2 : ℕ) + 1)) - ((D.R.t : ℚ) + 1) / 2⌋ +
        (((p.κ i).n / 2 : ℕ) : ℤ) := by
  have hk := D.R.m_add_three_le_k
  have hmain := GlobalTheory.CovTop.WtRead.main D p.T p.fw.laws i (p.κ i)
  have hsw : (D.R.sigW ((i : ℕ) + 1)).1 = D.R.k + (i : ℕ) := by simp only [Ranks.sigW]; omega
  have hpq : (dat p i).p = (D.R.sigW ((i : ℕ) + 1)).1 := hmain.1
  have hlt : D.R.k - 1 - 1 < (dat p i).p + (dat p i).q := by omega
  have hj : D.R.k - 2 < (D.R.sigW ((i : ℕ) + 1)).1 := by omega
  obtain ⟨-, hnn⟩ := GlobalTheory.RecGaps.bigEnt p P i t (D.R.k - 2) hj
  unfold anchor
  rw [dif_pos hlt, GlobalTheory.CovTop.WtRead.laOf_big D p.T p.fw.laws i (p.κ i) t τ hτ _ ⟨D.R.k - 2, hj⟩ (by simp; omega),
    (p.fw.kap i t).1 ⟨D.R.k - 2, hj⟩]
  rw [GlobalTheory.RecGaps.sig_Wc]
  unfold aPl
  rw [if_pos hj, Int.toNat_of_nonneg hnn]

theorem abs_anchor_sub_le (P : ParameterChoice' D L) (t : D.what₂.Tau) (τ : Psi p.T.Q.H) (hτ : τ.1 = DV.tauEmb D t) :
    |((anchor (dat p i) (wtA (p.κ i)) (p.κ i).n (D.R.k - 1) τ : ℤ) : ℝ) - (((D.hc t).e i : ℚ) : ℝ)| ≤
      L.Sc + D.R.nV + D.R.m + D.R.t + 2 := by
  have hk := D.R.m_add_three_le_k
  have ha := anchor_eq p i P t τ hτ
  have hn : (p.κ i).n = D.R.nV := (p.fw.kap i t).2.2
  have hv : Formalism.L2.NTheta.lamAt (D.hc t) (D.R.k - 2) = (D.hc t).v ⟨D.R.k - 2, by omega⟩ := by
    unfold Formalism.L2.NTheta.lamAt; rw [dif_pos (by omega)]
  have hc := L.cloud_v t ⟨D.R.k - 2, by omega⟩
  have hsw : ((D.R.sigW ((i : ℕ) + 1)).1 : ℚ) - ((D.R.k - 2 : ℕ) + 1) = (i : ℚ) + 1 := by
    rw [show (D.R.sigW ((i : ℕ) + 1)).1 = D.R.k + (i : ℕ) by simp only [Ranks.sigW]; omega,
      Nat.cast_sub (by omega : 2 ≤ D.R.k)]
    push_cast; ring
  rw [hsw, hv] at ha
  rw [ha, hn]
  have h1 := Int.floor_le ((D.hc t).v ⟨D.R.k - 2, by omega⟩ + (D.hc t).e i - ((i : ℚ) + 1) - ((D.R.t : ℚ) + 1) / 2)
  have h2 := Int.lt_floor_add_one ((D.hc t).v ⟨D.R.k - 2, by omega⟩ + (D.hc t).e i - ((i : ℚ) + 1) - ((D.R.t : ℚ) + 1) / 2)
  have h1' : ((⌊(D.hc t).v ⟨D.R.k - 2, by omega⟩ + (D.hc t).e i - ((i : ℚ) + 1) - ((D.R.t : ℚ) + 1) / 2⌋ : ℤ) : ℝ) ≤
      (((D.hc t).v ⟨D.R.k - 2, by omega⟩ + (D.hc t).e i - ((i : ℚ) + 1) - ((D.R.t : ℚ) + 1) / 2 : ℚ) : ℝ) := by
    exact_mod_cast h1
  have h2' : (((D.hc t).v ⟨D.R.k - 2, by omega⟩ + (D.hc t).e i - ((i : ℚ) + 1) - ((D.R.t : ℚ) + 1) / 2 : ℚ) : ℝ) <
      ((⌊(D.hc t).v ⟨D.R.k - 2, by omega⟩ + (D.hc t).e i - ((i : ℚ) + 1) - ((D.R.t : ℚ) + 1) / 2⌋ : ℤ) : ℝ) + 1 := by
    exact_mod_cast h2
  have hnv : ((D.R.nV / 2 : ℕ) : ℝ) ≤ D.R.nV := by exact_mod_cast Nat.div_le_self _ _
  have hnv0 : (0 : ℝ) ≤ ((D.R.nV / 2 : ℕ) : ℝ) := by positivity
  have hi : ((i : ℕ) : ℝ) + 1 ≤ D.R.m := by exact_mod_cast i.2
  have ht : (0 : ℝ) ≤ D.R.t := by positivity
  rw [Int.cast_add, Int.cast_natCast]
  push_cast at h1' h2'
  rw [abs_le]
  constructor <;> linarith [hc.1, hc.2]

set_option maxHeartbeats 1000000 in

theorem anchorAt_of {PP A : ℝ} (P : ParameterChoice' D L) (hw : WtNum p i PP) (hh : HostNum D L PP A 1) : AnchorAt p i 100 := by
  have hk := D.R.m_add_three_le_k
  have hm2 := D.R.two_le_m
  obtain ⟨hp, hq, hcard, -, -, E, hE, -⟩ := GlobalTheory.CovTop.WtRead.main D p.T p.fw.laws i (p.κ i)
  have hL10 := hh.big.2.1
  have hLx := hh.big.2.2.1
  have hll := hh.big.2.2.2
  have hxA : 1 ≤ L.sc.x ^ A := Real.one_le_rpow (by linarith) (by linarith [hh.poly.1])
  have hb : L.sc.x ^ A ≤ L.sc.b := by simpa using hh.room
  have hb1 : 1 ≤ L.sc.b := hxA.trans hb
  have hf : (8 : ℝ) ≤ D.R.f := by exact_mod_cast hh.f8
  have hm : (2 : ℝ) ≤ D.R.m := by exact_mod_cast hm2
  have hunit := hw.unit
  have hom := hw.om
  have hanc : ∀ τ, |((anchor (dat p i) (wtA (p.κ i)) (p.κ i).n (D.R.k - 1) τ : ℤ) : ℝ)| ≤ 4 * L.sc.b := by
    intro τ
    unfold anchor
    split_ifs with h
    · exact hw.up τ _
    · simp only [Int.cast_zero, abs_zero]; linarith

  have hpr : ((dat p i).p : ℝ) + (dat p i).q = D.R.r := by
    rw [hp, hq]; exact_mod_cast GlobalTheory.CovTop.WtRead.sigW_add D i
  have hp0 : (0 : ℝ) ≤ (dat p i).p := by positivity
  have hq0 : (0 : ℝ) ≤ (dat p i).q := by positivity
  have hcr : |((dat p i).p : ℝ) - (dat p i).q| ≤ D.R.r := abs_le.2 ⟨by linarith, by linarith⟩
  have hqm : ((dat p i).q : ℝ) ≤ D.R.m := by
    rw [hq]; exact_mod_cast (by simp only [Ranks.sigW]; omega : (D.R.sigW ((i : ℕ) + 1)).2 ≤ D.R.m)
  have hc_eq : ((D.R.k : ℝ) + (((i : ℕ) + 1 : ℕ) : ℝ) - 1) - ((D.R.m : ℝ) - (((i : ℕ) + 1 : ℕ) : ℝ)) =
      ((dat p i).p : ℝ) - (dat p i).q := by
    rw [hp, hq]
    simp only [Ranks.sigW]
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
    push_cast; ring

  have hmainS : mainT p i = ∑ t : D.what₂.Tau, (((dat p i).p : ℝ) - (dat p i).q) * (((D.hc t).e i : ℚ) : ℝ) *
      (ofRecord D L p.Del p.h0).logOm := by
    show ∑ ρ : RPl D.R, (((D.R.k : ℝ) + (((i : ℕ) + 1 : ℕ) : ℝ) - 1) - ((D.R.m : ℝ) - (((i : ℕ) + 1 : ℕ) : ℝ))) *
      (ofRecord D L p.Del p.h0).w ((i : ℕ) + 1) ρ * (ofRecord D L p.Del p.h0).logOm = _
    rw [hc_eq, ← (tauPl_bijective D).sum_comp (fun t => (((dat p i).p : ℝ) - (dat p i).q) * (((D.hc t).e i : ℚ) : ℝ) *
      (ofRecord D L p.Del p.h0).logOm)]
    refine Finset.sum_congr rfl fun ρ _ => ?_
    congr 2
    simp only [NumDatum.w, NumDatum.eQ]
    rw [dif_pos ⟨by omega, by omega⟩]
    congr 3
  have hancS : ∑ τ : Psi p.T.Q.H, (((dat p i).p : ℝ) - (dat p i).q) *
      ((anchor (dat p i) (wtA (p.κ i)) (p.κ i).n (D.R.k - 1) τ : ℤ) : ℝ) * (ofRecord D L p.Del p.h0).logOm =
      ∑ t : D.what₂.Tau, (((dat p i).p : ℝ) - (dat p i).q) *
        ((anchor (dat p i) (wtA (p.κ i)) (p.κ i).n (D.R.k - 1) (E t) : ℤ) : ℝ) * (ofRecord D L p.Del p.h0).logOm :=
    (Equiv.sum_comp E (fun τ => (((dat p i).p : ℝ) - (dat p i).q) *
      ((anchor (dat p i) (wtA (p.κ i)) (p.κ i).n (D.R.k - 1) τ : ℤ) : ℝ) * (ofRecord D L p.Del p.h0).logOm)).symm
  have hcardT : (Fintype.card D.what₂.Tau : ℝ) = D.R.f := by exact_mod_cast Formalism.MainNotions.Lnk.card_Tau D

  have hne : Nonempty D.what₂.Tau := Fintype.card_pos_iff.1 (by rw [Formalism.MainNotions.Lnk.card_Tau]; have := hh.f8; omega)
  obtain ⟨t0⟩ := hne
  have hw'' : L.sc.w'' D.R.n ≤ 8 * L.sc.b := by
    have a1 := hw.low (E t0)
    have a2 := (abs_le.1 (hanc (E t0))).2
    linarith
  have hr2k : (D.R.r : ℝ) ≤ 2 * D.R.k := by exact_mod_cast (by unfold Ranks.r; omega : D.R.r ≤ 2 * D.R.k)
  have hSc0 : 0 ≤ L.Sc := L.Sc_pos.le
  have hrS : (D.R.r : ℝ) * L.Sc ≤ 16 * L.sc.b := by
    have a1 := P.kS_le
    have a2 : (D.R.r : ℝ) * L.Sc ≤ 2 * D.R.k * L.Sc := mul_le_mul_of_nonneg_right hr2k hSc0
    linarith
  have hnV : (D.R.nV : ℝ) = D.R.r + D.R.t := by unfold Ranks.nV; push_cast; ring
  have hmr : (D.R.m : ℝ) ≤ D.R.r := by exact_mod_cast (by unfold Ranks.r; omega : D.R.m ≤ D.R.r)
  have ht0 : (0 : ℝ) ≤ D.R.t := by positivity
  have hrnV : (D.R.r : ℝ) * D.R.nV ≤ L.sc.b := by
    have a1 := hh.poly.2.2
    have e0 : (0 : ℝ) ≤ (D.R.r : ℝ) * D.R.nV := by positivity
    have a2 : (D.R.r : ℝ) * D.R.nV * 1 ≤ (D.R.r : ℝ) * D.R.nV * (D.R.f * L.sc.L) :=
      mul_le_mul_of_nonneg_left (one_le_mul_of_one_le_of_one_le (by linarith) (by linarith)) e0
    calc (D.R.r : ℝ) * D.R.nV = (D.R.r : ℝ) * D.R.nV * 1 := by ring
      _ ≤ (D.R.r : ℝ) * D.R.nV * (D.R.f * L.sc.L) := a2
      _ = D.R.f * D.R.r * D.R.nV * L.sc.L := by ring
      _ ≤ L.sc.x ^ A := a1
      _ ≤ L.sc.b := hb
  have hB : (D.R.r : ℝ) * (L.Sc + D.R.nV + D.R.m + D.R.t + 2) ≤ 20 * L.sc.b := by
    have e1 : (D.R.r : ℝ) * (D.R.nV + D.R.m + D.R.t + 2) ≤ 4 * ((D.R.r : ℝ) * D.R.nV) := by
      calc (D.R.r : ℝ) * (D.R.nV + D.R.m + D.R.t + 2) ≤ (D.R.r : ℝ) * (4 * D.R.nV) :=
            mul_le_mul_of_nonneg_left (by linarith) (by positivity)
        _ = 4 * ((D.R.r : ℝ) * D.R.nV) := by ring
    calc (D.R.r : ℝ) * (L.Sc + D.R.nV + D.R.m + D.R.t + 2) =
          (D.R.r : ℝ) * L.Sc + (D.R.r : ℝ) * (D.R.nV + D.R.m + D.R.t + 2) := by ring
      _ ≤ 16 * L.sc.b + 4 * L.sc.b := add_le_add hrS (by linarith)
      _ = 20 * L.sc.b := by ring
  refine ⟨?_, ?_, hh.poly.2.2.trans hb⟩
  · rw [hmainS, hancS, ← Finset.sum_sub_distrib]
    have hterm : ∀ t : D.what₂.Tau, |(((dat p i).p : ℝ) - (dat p i).q) * (((D.hc t).e i : ℚ) : ℝ) *
        (ofRecord D L p.Del p.h0).logOm - (((dat p i).p : ℝ) - (dat p i).q) *
        ((anchor (dat p i) (wtA (p.κ i)) (p.κ i).n (D.R.k - 1) (E t) : ℤ) : ℝ) * (ofRecord D L p.Del p.h0).logOm| ≤
        (D.R.r : ℝ) * (L.Sc + D.R.nV + D.R.m + D.R.t + 2) * (3 * L.sc.L) := by
      intro t
      have a1 := abs_anchor_sub_le p i P t (E t) (hE t)
      rw [show (((dat p i).p : ℝ) - (dat p i).q) * (((D.hc t).e i : ℚ) : ℝ) * (ofRecord D L p.Del p.h0).logOm -
          (((dat p i).p : ℝ) - (dat p i).q) * ((anchor (dat p i) (wtA (p.κ i)) (p.κ i).n (D.R.k - 1) (E t) : ℤ) : ℝ) *
          (ofRecord D L p.Del p.h0).logOm = -((((dat p i).p : ℝ) - (dat p i).q) *
          (((anchor (dat p i) (wtA (p.κ i)) (p.κ i).n (D.R.k - 1) (E t) : ℤ) : ℝ) - (((D.hc t).e i : ℚ) : ℝ)) *
          (ofRecord D L p.Del p.h0).logOm) by ring, abs_neg, abs_mul, abs_mul]
      exact mul_le_mul (mul_le_mul hcr a1 (abs_nonneg _) (by positivity)) hom (abs_nonneg _) (by positivity)
    calc _ ≤ ∑ t : D.what₂.Tau, (D.R.r : ℝ) * (L.Sc + D.R.nV + D.R.m + D.R.t + 2) * (3 * L.sc.L) :=
          (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun t _ => hterm t)
      _ = D.R.f * ((D.R.r : ℝ) * (L.Sc + D.R.nV + D.R.m + D.R.t + 2)) * (3 * L.sc.L) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcardT]; ring
      _ ≤ D.R.f * (20 * L.sc.b) * (3 * L.sc.L) := by gcongr
      _ ≤ 100 * unitE p := by
          rw [hunit]
          have e1 : (0 : ℝ) ≤ D.R.f * L.sc.b * L.sc.L := by positivity
          have e2 : D.R.f * L.sc.b * L.sc.L * 1 ≤ D.R.f * L.sc.b * L.sc.L * (D.R.m * Real.log (Real.log L.sc.x)) :=
            mul_le_mul_of_nonneg_left (one_le_mul_of_one_le_of_one_le (by linarith) hll) e1
          have e3 : (D.R.f : ℝ) * D.R.m * L.sc.b * L.sc.L * Real.log (Real.log L.sc.x) =
              D.R.f * L.sc.b * L.sc.L * (D.R.m * Real.log (Real.log L.sc.x)) := by ring
          have e4 : (D.R.f : ℝ) * (20 * L.sc.b) * (3 * L.sc.L) = 60 * (D.R.f * L.sc.b * L.sc.L * 1) := by ring
          rw [e3, e4]
          linarith
  · have hsum : ∑ τ : Psi p.T.Q.H, |((anchor (dat p i) (wtA (p.κ i)) (p.κ i).n (D.R.k - 1) τ : ℤ) : ℝ)| ≤
        D.R.f * (4 * L.sc.b) := by
      calc _ ≤ ∑ τ : Psi p.T.Q.H, 4 * L.sc.b := Finset.sum_le_sum fun τ _ => hanc τ
        _ = _ := by rw [Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card, hcard, nsmul_eq_mul]
    calc (∑ τ : Psi p.T.Q.H, |((anchor (dat p i) (wtA (p.κ i)) (p.κ i).n (D.R.k - 1) τ : ℤ) : ℝ)|) *
          ((dat p i).q : ℝ) * L.sc.L ≤ D.R.f * (4 * L.sc.b) * D.R.m * L.sc.L := by gcongr
      _ ≤ 100 * unitE p := by
          rw [hunit]
          have e1 : (0 : ℝ) ≤ D.R.f * L.sc.b * D.R.m * L.sc.L := by positivity
          have e2 : D.R.f * L.sc.b * D.R.m * L.sc.L * 1 ≤ D.R.f * L.sc.b * D.R.m * L.sc.L * Real.log (Real.log L.sc.x) :=
            mul_le_mul_of_nonneg_left hll e1
          have e3 : (D.R.f : ℝ) * D.R.m * L.sc.b * L.sc.L * Real.log (Real.log L.sc.x) =
              D.R.f * L.sc.b * D.R.m * L.sc.L * Real.log (Real.log L.sc.x) := by ring
          have e4 : (D.R.f : ℝ) * (4 * L.sc.b) * D.R.m * L.sc.L = 4 * (D.R.f * L.sc.b * D.R.m * L.sc.L * 1) := by ring
          rw [e3, e4]
          linarith

end GlobalTheory.CovTop.AnchorRd

namespace GlobalTheory.CovTop

theorem anchor_holds : Anchor := by
  refine Closed.imp (Closed.and WtShape.wtN (Sizes.hostN 1)) ?_
  rintro eps Fm CH - ⟨⟨C1, -, hW⟩, ⟨A, -, hH⟩⟩
  obtain ⟨x0, h⟩ := EvTied.and hW hH
  exact ⟨100, by norm_num, x0, fun x hx hle ι p hp i =>
    AnchorRd.anchorAt_of p i (Fm.params x hx ι) ((h x hx hle ι p hp).1 i) ((h x hx hle ι p hp).2 i)⟩

end GlobalTheory.CovTop
