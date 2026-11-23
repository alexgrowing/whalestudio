import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ComponentModelWeightDimensionDictionary
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.WeightFloorInequalities
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.NumericalConsequencesOfPins

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop
  GlobalTheory.CompHS GlobalTheory.HSApp

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.RecGaps

open Formalism.BasicNotions Formalism.L2.Pj Formalism.L2.NTheta

variable {R : Ranks}

theorem lam_step (h : HCParam R) (n : ℕ) (hn : n + 1 < R.r) :
    ∃ z : ℤ, lamAt h n - lamAt h (n + 1) = z ∧ 1 ≤ z := by
  obtain ⟨a, ha⟩ := lamAt_int h n
  obtain ⟨b, hb⟩ := lamAt_int h (n + 1)
  have hl := lamAt_lt h n hn
  rw [ha, hb] at hl ⊢
  refine ⟨a - b, by push_cast; ring, ?_⟩
  have : b < a := by exact_mod_cast hl
  omega

theorem lam_mono (h : HCParam R) (a : ℕ) : ∀ d : ℕ, a + d < R.r → lamAt h (a + d) + d ≤ lamAt h a := by
  intro d
  induction d with
  | zero => intro _; simp
  | succ d ih =>
    intro hd
    have h1 := ih (by omega)
    obtain ⟨z, hz, hz1⟩ := lam_step h (a + d) (by omega)
    have : (1 : ℚ) ≤ z := by exact_mod_cast hz1
    rw [← add_assoc] at hd ⊢
    push_cast
    linarith

theorem lam_b (h : HCParam R) (l : ℕ) (hl : l < R.m) : lamAt h (R.k - 1 + l) = -h.b ⟨l, hl⟩ := by
  unfold lamAt
  rw [dif_neg (by omega)]
  have e : R.k - 1 + l - (R.k - 1) = l := by omega
  rw [dif_pos (by omega)]
  congr 2
  exact Fin.ext e

theorem lam_gapS {D : D7} {L : SizeData₂ D} (P : ParameterChoice' D L) (t : D.what₂.Tau) (n : ℕ) (hn : n + 1 < D.R.r) :
    LevelStarExponents.gapS D P.Cgap < ((lamAt (D.hc t) n - lamAt (D.hc t) (n + 1) : ℚ) : ℝ) := by
  obtain ⟨s1, s2, s3⟩ := P.sig_gaps t
  have hk := D.R.m_add_three_le_k
  have hm := D.R.two_le_m
  have hr : D.R.r = D.R.k + D.R.m - 1 := rfl
  by_cases h1 : n + 1 < D.R.k - 1
  · have e1 : lamAt (D.hc t) n = (D.hc t).v ⟨n, by omega⟩ := by unfold lamAt; rw [dif_pos (by omega)]
    have e2 : lamAt (D.hc t) (n + 1) = (D.hc t).v ⟨n + 1, h1⟩ := by unfold lamAt; rw [dif_pos h1]
    rw [e1, e2]; exact s1 n h1
  · by_cases h2 : n + 1 = D.R.k - 1
    · have e1 : lamAt (D.hc t) n = (D.hc t).v ⟨D.R.k - 2, by omega⟩ := by
        unfold lamAt; rw [dif_pos (by omega)]; congr 1; exact Fin.ext (by simp; omega)
      have e2 : lamAt (D.hc t) (n + 1) = -(D.hc t).b ⟨0, by omega⟩ := by
        have := lam_b (D.hc t) 0 (by omega)
        rw [show n + 1 = D.R.k - 1 + 0 by omega]; exact this
      rw [e1, e2, sub_neg_eq_add]; exact s2 (by omega) (by omega)
    · have hj : n + 1 - (D.R.k - 1) < D.R.m := by omega
      have e1 : lamAt (D.hc t) n = -(D.hc t).b ⟨n - (D.R.k - 1), by omega⟩ := by
        have := lam_b (D.hc t) (n - (D.R.k - 1)) (by omega)
        rwa [show D.R.k - 1 + (n - (D.R.k - 1)) = n by omega] at this
      have e2 : lamAt (D.hc t) (n + 1) = -(D.hc t).b ⟨n - (D.R.k - 1) + 1, by omega⟩ := by
        have := lam_b (D.hc t) (n - (D.R.k - 1) + 1) (by omega)
        rwa [show D.R.k - 1 + (n - (D.R.k - 1) + 1) = n + 1 by omega] at this
      rw [e1, e2, neg_sub_neg]; exact s3 (n - (D.R.k - 1)) (by omega)

section Ent

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D}
  {Kc : Formalism.MainNotions.G.Consts} {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ}

open GlobalTheory.BigTop Formalism.IndefR.Links

theorem sig_Wc (i : Fin D.R.m) (t : D.what₂.Tau) :
    (Wc D i).sig (Formalism.BasicNotions.TH.tauE D t) = D.R.sigW ((i : ℕ) + 1) :=
  D.sp.W_sigval _ (by omega) (by have := i.2; omega) _

theorem two_nodeGap_add_six_le_roundingConstant (P : ParameterChoice' D L) : 2 * (D.R.t : ℝ) + 6 ≤ LevelStarExponents.h0 L := by
  have h := P.h0_ge.2.2.2.2.1
  have : (0 : ℝ) ≤ 4 * (D.R.N D.R.m : ℝ) ^ 3 := by positivity
  linarith

theorem bigEnt (p : PtAt ex Csz) (P : ParameterChoice' D L) (i : Fin D.R.m) (t : D.what₂.Tau) (j : ℕ)
    (hj : j < (D.R.sigW ((i : ℕ) + 1)).1) :
    ((wtA (p.κ i) (DV.tauEmb D t, j) : ℕ) : ℤ) =
      ⌊lamAt (D.hc t) j + (D.hc t).e i - (((D.R.sigW ((i : ℕ) + 1)).1 : ℚ) - (j + 1)) - ((D.R.t : ℚ) + 1) / 2⌋ ∧
    0 ≤ ⌊lamAt (D.hc t) j + (D.hc t).e i - (((D.R.sigW ((i : ℕ) + 1)).1 : ℚ) - (j + 1)) - ((D.R.t : ℚ) + 1) / 2⌋ := by
  have hnn : 0 ≤ ⌊lamAt (D.hc t) j + (D.hc t).e i - (((D.R.sigW ((i : ℕ) + 1)).1 : ℚ) - (j + 1)) -
      ((D.R.t : ℚ) + 1) / 2⌋ := by
    apply Int.floor_nonneg.2
    have hsw : (D.R.sigW ((i : ℕ) + 1)).1 = D.R.k + (i : ℕ) := by simp only [Ranks.sigW]; omega
    obtain ⟨d, hd⟩ : ∃ d, D.R.k + (i : ℕ) = j + d + 1 := ⟨D.R.k + (i : ℕ) - j - 1, by omega⟩
    have hk := D.R.m_add_three_le_k
    have hm := D.R.m_le_f
    have hr : D.R.r = D.R.k + D.R.m - 1 := rfl
    have hmono := lam_mono (D.hc t) j d (by have := i.2; omega)
    have hb := lam_b (D.hc t) (i : ℕ) i.2
    rw [show j + d = D.R.k - 1 + (i : ℕ) by omega, hb] at hmono
    have hce := P.e_centred t i
    have h0t := two_nodeGap_add_six_le_roundingConstant P
    have hcast : (((D.R.sigW ((i : ℕ) + 1)).1 : ℚ) - (j + 1)) = d := by
      rw [hsw, hd]; push_cast; ring
    rw [hcast]
    have key : (0 : ℝ) ≤ ((lamAt (D.hc t) j + (D.hc t).e i - d - ((D.R.t : ℚ) + 1) / 2 : ℚ) : ℝ) := by
      have hm' : (((-(D.hc t).b i + d : ℚ)) : ℝ) ≤ ((lamAt (D.hc t) j : ℚ) : ℝ) := by exact_mod_cast hmono
      have hce' := (abs_le.1 hce).1
      push_cast at hm' hce' ⊢
      have : (i : Fin D.R.m) = ⟨(i : ℕ), i.2⟩ := rfl
      linarith
    exact_mod_cast key
  refine ⟨?_, hnn⟩
  rw [GlobalTheory.Shares.WtDic.wtA_tau]
  unfold ext0
  rw [dif_pos hj, (p.fw.kap i t).1 ⟨j, hj⟩, sig_Wc]
  unfold aPl
  rw [if_pos hj]
  exact Int.toNat_of_nonneg hnn

theorem smallEnt (p : PtAt ex Csz) (P : ParameterChoice' D L) (i : Fin D.R.m) (t : D.what₂.Tau) (s : ℕ)
    (hs : s < (D.R.sigW ((i : ℕ) + 1)).2) :
    ((wtA (p.κ i) (conjEmb (DV.tauEmb D t), (D.R.sigW ((i : ℕ) + 1)).2 - 1 - s) : ℕ) : ℤ) =
      ⌊-((D.hc t).e i + lamAt (D.hc t) ((D.R.sigW ((i : ℕ) + 1)).1 + s) + ((s : ℚ) + 1) + ((D.R.t : ℚ) - 1) / 2)⌋ ∧
    0 ≤ ⌊-((D.hc t).e i + lamAt (D.hc t) ((D.R.sigW ((i : ℕ) + 1)).1 + s) + ((s : ℚ) + 1) + ((D.R.t : ℚ) - 1) / 2)⌋ := by
  have hsw1 : (D.R.sigW ((i : ℕ) + 1)).1 = D.R.k + (i : ℕ) := by simp only [Ranks.sigW]; omega
  have hsw2 : (D.R.sigW ((i : ℕ) + 1)).2 = D.R.m - ((i : ℕ) + 1) := rfl
  have hnn : 0 ≤ ⌊-((D.hc t).e i + lamAt (D.hc t) ((D.R.sigW ((i : ℕ) + 1)).1 + s) + ((s : ℚ) + 1) +
      ((D.R.t : ℚ) - 1) / 2)⌋ := by
    apply Int.floor_nonneg.2
    have hk := D.R.m_add_three_le_k
    have hr : D.R.r = D.R.k + D.R.m - 1 := rfl
    have hi1 : (i : ℕ) + 1 < D.R.m := by omega
    have hmono := lam_mono (D.hc t) ((D.R.sigW ((i : ℕ) + 1)).1) s (by omega)
    have hb := lam_b (D.hc t) ((i : ℕ) + 1) hi1
    rw [show D.R.k - 1 + ((i : ℕ) + 1) = (D.R.sigW ((i : ℕ) + 1)).1 by omega] at hb
    rw [hb] at hmono
    have hce := P.e_centred t i
    have hng := (P.nodes_gap t (i : ℕ) hi1).1
    have h0t := two_nodeGap_add_six_le_roundingConstant P
    have key : (0 : ℝ) ≤ ((-((D.hc t).e i + lamAt (D.hc t) ((D.R.sigW ((i : ℕ) + 1)).1 + s) + ((s : ℚ) + 1) +
        ((D.R.t : ℚ) - 1) / 2) : ℚ) : ℝ) := by
      have hm' : (((lamAt (D.hc t) ((D.R.sigW ((i : ℕ) + 1)).1 + s) + s : ℚ)) : ℝ) ≤
          ((-(D.hc t).b ⟨(i : ℕ) + 1, hi1⟩ : ℚ) : ℝ) := by exact_mod_cast hmono
      have hce' := (abs_le.1 hce).2
      push_cast at hm' hce' hng ⊢
      have : (i : Fin D.R.m) = ⟨(i : ℕ), i.2⟩ := rfl
      linarith
    exact_mod_cast key
  refine ⟨?_, hnn⟩
  rw [GlobalTheory.Shares.WtDic.wtA_conj]
  unfold ext0
  rw [dif_pos (by omega), (p.fw.kap i t).2.1 ⟨_, by omega⟩, sig_Wc]
  unfold aMi
  rw [if_pos (by omega)]
  have e1 : (D.R.sigW ((i : ℕ) + 1)).2 - ((D.R.sigW ((i : ℕ) + 1)).2 - 1 - s) = s + 1 := by omega
  have e2 : (D.R.sigW ((i : ℕ) + 1)).1 + (s + 1) - 1 = (D.R.sigW ((i : ℕ) + 1)).1 + s := by omega
  simp only [e1, e2]
  push_cast
  exact Int.toNat_of_nonneg hnn

end Ent

open GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.CompHS in

theorem gaps : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D}
    {Kc : Formalism.MainNotions.G.Consts} {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ}
    (p : PtAt ex Csz) (P : ParameterChoice' D L) (i : Fin D.R.m), (i : ℕ) + 1 < D.R.m →
    (dat p i).p + (dat p i).q = D.R.r ∧ GlobalTheory.FlagTan.dimFlag (dat p i) = D.R.f * D.R.r.choose 2 ∧
    ∀ (τ : Psi p.T.Q.H) (k : ℕ), k + 1 < (dat p i).p + (dat p i).q →
      (k + 1 ≠ (dat p i).p → min (LevelStarExponents.gapS D P.Cgap) (LevelStarExponents.h0 L) - 2 ≤ (gap (uW p i τ) k : ℝ)) ∧
      (k + 1 = (dat p i).p → LevelStarExponents.h0 L + D.R.r - 3 ≤ (gap (uW p i τ) k : ℝ)) := by
  intro D L hT Gi Gl Kc Y0 cX ex Csz p P i hi
  have hQ : p.T.Q.Pins := p.fw.laws.pins
  have hj : InR D ((i : ℕ) + 1) := ⟨by omega, by omega⟩
  obtain ⟨hp, hq, -⟩ := hQ.2.2.2 _ hj
  have hp' : (dat p i).p = (D.R.sigW ((i : ℕ) + 1)).1 := hp
  have hq' : (dat p i).q = (D.R.sigW ((i : ℕ) + 1)).2 := hq
  have hk0 := D.R.m_add_three_le_k
  have hr : D.R.r = D.R.k + D.R.m - 1 := rfl
  have hpq : (dat p i).p + (dat p i).q = D.R.r := by rw [hp', hq']; simp only [Ranks.sigW]; omega
  refine ⟨hpq, ?_, ?_⟩
  · unfold GlobalTheory.FlagTan.dimFlag
    rw [hpq, GlobalTheory.PinNum.finrank_host D, Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)]
  · intro τ k hk
    obtain ⟨t, ht⟩ := ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.exists_tau_of_inPsi p.T.Q hQ.1 τ.1 τ.2

    have hn := (p.fw.kap i t).2.2
    have hgap : gap (uW p i τ) k =
        (if k < (D.R.sigW ((i : ℕ) + 1)).1 then ((wtA (p.κ i) (DV.tauEmb D t, k) : ℕ) : ℤ) + ((D.R.nV / 2 : ℕ) : ℤ)
          else -((wtA (p.κ i) (conjEmb (DV.tauEmb D t), (D.R.sigW ((i : ℕ) + 1)).2 - 1 - (k - (D.R.sigW ((i : ℕ) + 1)).1)) : ℕ) : ℤ)
            - ((D.R.nV / 2 : ℕ) : ℤ)) -
        (if k + 1 < (D.R.sigW ((i : ℕ) + 1)).1 then ((wtA (p.κ i) (DV.tauEmb D t, k + 1) : ℕ) : ℤ) + ((D.R.nV / 2 : ℕ) : ℤ)
          else -((wtA (p.κ i) (conjEmb (DV.tauEmb D t), (D.R.sigW ((i : ℕ) + 1)).2 - 1 - (k + 1 - (D.R.sigW ((i : ℕ) + 1)).1)) : ℕ) : ℤ)
            - ((D.R.nV / 2 : ℕ) : ℤ)) := by
      unfold gap
      rw [dif_pos hk]
      simp only [uW, uWt, Pi.sub_apply, GlobalTheory.FlatLine.parWt, laOf, weightOf, hp', hq', ht, hn]
      ring
    rw [hgap, hp']

    have hPQ : (D.R.sigW ((i : ℕ) + 1)).1 + (D.R.sigW ((i : ℕ) + 1)).2 = D.R.r := by rw [← hp', ← hq']; exact hpq
    rw [hp', hq'] at hk
    have hPv : (D.R.sigW ((i : ℕ) + 1)).1 = D.R.k + (i : ℕ) := by simp only [Ranks.sigW]; omega
    have hev : Even D.R.nV := hn ▸ (p.κ i).n_even
    have hgS : 0 < LevelStarExponents.gapS D P.Cgap := by
      unfold LevelStarExponents.gapS
      have := P.Cgap_pos
      have hm := D.R.two_le_m
      have : (0 : ℝ) < (D.R.k : ℝ) := by exact_mod_cast (show 0 < D.R.k by omega)
      positivity
    rcases lt_trichotomy (k + 1) (D.R.sigW ((i : ℕ) + 1)).1 with hA | hB | hC
    · rw [if_pos (by omega), if_pos hA]
      obtain ⟨e1, -⟩ := bigEnt p P i t k (by omega)
      obtain ⟨e2, -⟩ := bigEnt p P i t (k + 1) hA
      rw [e1, e2]
      obtain ⟨z, hz, -⟩ := lam_step (D.hc t) k (by omega)
      have hfl : ⌊lamAt (D.hc t) k + (D.hc t).e i - ((((D.R.sigW ((i : ℕ) + 1)).1 : ℕ) : ℚ) - ((k : ℚ) + 1)) - ((D.R.t : ℚ) + 1) / 2⌋ =
          ⌊lamAt (D.hc t) (k + 1) + (D.hc t).e i - ((((D.R.sigW ((i : ℕ) + 1)).1 : ℕ) : ℚ) - (((k + 1 : ℕ) : ℚ) + 1)) -
            ((D.R.t : ℚ) + 1) / 2⌋ + (z - 1) := by
        rw [← Int.floor_add_intCast]; congr 1; push_cast; linarith
      rw [hfl]
      refine ⟨fun _ => ?_, fun h => absurd h (by omega)⟩
      have hg := lam_gapS P t k (by omega)
      rw [hz] at hg
      push_cast at hg ⊢
      have := min_le_left (LevelStarExponents.gapS D P.Cgap) (LevelStarExponents.h0 L)
      linarith
    · rw [if_pos (by omega), if_neg (by omega), show k + 1 - (D.R.sigW ((i : ℕ) + 1)).1 = 0 by omega]
      obtain ⟨e1, -⟩ := bigEnt p P i t k (by omega)
      obtain ⟨e2, -⟩ := smallEnt p P i t 0 (by omega)
      rw [e1, e2]
      refine ⟨fun h => absurd h (by omega), fun _ => ?_⟩
      have hi1 : (i : ℕ) + 1 < D.R.m := hi
      have hb0 := lam_b (D.hc t) (i : ℕ) i.2
      have hb1 := lam_b (D.hc t) ((i : ℕ) + 1) hi1
      rw [show D.R.k - 1 + (i : ℕ) = k by omega] at hb0
      rw [show D.R.k - 1 + ((i : ℕ) + 1) = (D.R.sigW ((i : ℕ) + 1)).1 + 0 by omega] at hb1
      have hX := Int.sub_one_lt_floor (lamAt (D.hc t) k + (D.hc t).e i - ((((D.R.sigW ((i : ℕ) + 1)).1 : ℕ) : ℚ) - ((k : ℚ) + 1)) -
        ((D.R.t : ℚ) + 1) / 2)
      have hY := Int.sub_one_lt_floor (-((D.hc t).e i + lamAt (D.hc t) ((D.R.sigW ((i : ℕ) + 1)).1 + 0) + (((0 : ℕ) : ℚ) + 1) +
        ((D.R.t : ℚ) - 1) / 2))
      have hkq : (((D.R.sigW ((i : ℕ) + 1)).1 : ℕ) : ℝ) = (k : ℝ) + 1 := by rw [← hB]; push_cast; ring
      have hb0' : ((lamAt (D.hc t) k : ℚ) : ℝ) = -(((D.hc t).b i : ℚ) : ℝ) := by rw [hb0]; push_cast; ring
      have hb1' : ((lamAt (D.hc t) ((D.R.sigW ((i : ℕ) + 1)).1 + 0) : ℚ) : ℝ) = -(((D.hc t).b ⟨(i : ℕ) + 1, hi1⟩ : ℚ) : ℝ) := by
        rw [hb1]; push_cast; ring
      have hX' := (Rat.cast_lt (K := ℝ)).2 hX
      have hY' := (Rat.cast_lt (K := ℝ)).2 hY
      have hng := (P.nodes_gap t (i : ℕ) hi1).1
      have hc2z : ((D.R.nV / 2 : ℕ) : ℤ) * 2 = (D.R.r : ℤ) + D.R.t := by
        have := Nat.div_two_mul_two_of_even hev
        unfold Ranks.nV at this ⊢; omega
      generalize ((D.R.nV / 2 : ℕ) : ℤ) = c at hc2z ⊢
      have hc2r : (c : ℝ) * 2 = (D.R.r : ℝ) + D.R.t := by exact_mod_cast hc2z
      push_cast at hX' hY' hng ⊢
      have : (i : Fin D.R.m) = ⟨(i : ℕ), i.2⟩ := rfl
      rw [← this] at hng
      linarith
    · obtain ⟨s, rfl⟩ : ∃ s, k = (D.R.sigW ((i : ℕ) + 1)).1 + s := ⟨k - (D.R.sigW ((i : ℕ) + 1)).1, by omega⟩
      rw [if_neg (by omega), if_neg (by omega), show (D.R.sigW ((i : ℕ) + 1)).1 + s - (D.R.sigW ((i : ℕ) + 1)).1 = s by omega,
        show (D.R.sigW ((i : ℕ) + 1)).1 + s + 1 - (D.R.sigW ((i : ℕ) + 1)).1 = s + 1 by omega]
      obtain ⟨e1, -⟩ := smallEnt p P i t s (by omega)
      obtain ⟨e2, -⟩ := smallEnt p P i t (s + 1) (by omega)
      rw [e1, e2]
      obtain ⟨z, hz, -⟩ := lam_step (D.hc t) ((D.R.sigW ((i : ℕ) + 1)).1 + s) (by omega)
      have hfl : ⌊-((D.hc t).e i + lamAt (D.hc t) ((D.R.sigW ((i : ℕ) + 1)).1 + (s + 1)) + (((s + 1 : ℕ) : ℚ) + 1) + ((D.R.t : ℚ) - 1) / 2)⌋ =
          ⌊-((D.hc t).e i + lamAt (D.hc t) ((D.R.sigW ((i : ℕ) + 1)).1 + s) + ((s : ℚ) + 1) + ((D.R.t : ℚ) - 1) / 2)⌋ + (z - 1) := by
        rw [← Int.floor_add_intCast]; congr 1
        rw [show (D.R.sigW ((i : ℕ) + 1)).1 + (s + 1) = (D.R.sigW ((i : ℕ) + 1)).1 + s + 1 by ring]
        push_cast; linarith
      rw [hfl]
      refine ⟨fun _ => ?_, fun h => absurd h (by omega)⟩
      have hg := lam_gapS P t ((D.R.sigW ((i : ℕ) + 1)).1 + s) (by omega)
      rw [hz] at hg
      push_cast at hg ⊢
      have := min_le_left (LevelStarExponents.gapS D P.Cgap) (LevelStarExponents.h0 L)
      linarith

end GlobalTheory.RecGaps

end
