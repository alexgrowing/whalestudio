import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.QuoIff
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsCoreGoodMatch
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatLineThetaRootTwistTwistingSectionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightBoundHoldsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HostBoundHolds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatLineC1LogBoundStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnramifiedPointsDeepLevelStatement

set_option synthInstance.maxHeartbeats 400000

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2 Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.FlatLine GlobalTheory.FlatTw

namespace GlobalTheory.FlatSplit

section Congr

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ} {D : D7}

theorem lieFacZ_congr (x : ℝ) {G G' : WTZ E} (h : exZ Dw G = exZ Dw G') : lieFacZ Dw x G = lieFacZ Dw x G' := by
  unfold lieFacZ
  congr 4
  refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun i _ => ?_
  exact congrArg (fun z : ℤ => (z : ℝ)) (congrFun h (some ⟨τ, i⟩))

theorem lat_congr {C C' : Submodule c.F (Rul Xo c)} (hC : C = C') {N N' : (c.F →+* ℂ) → Rul Xo c → ℝ} (hN : N = N') :
    ((HasGram (fun σ (f : C) => N σ f) ∧ (supLat C).FG ∧ Submodule.span c.F (supLat C : Set C) = ⊤) ↔
      (HasGram (fun σ (f : C') => N' σ f) ∧ (supLat C').FG ∧ Submodule.span c.F (supLat C' : Set C') = ⊤)) ∧
    Formalism.HN.rkK (supLat C) = Formalism.HN.rkK (supLat C') ∧
    slope_sq (fun σ (f : C) => N σ f) (supLat C) = slope_sq (fun σ (f : C') => N' σ f) (supLat C') := by
  subst hC hN
  exact ⟨Iff.rfl, rfl, rfl⟩

theorem congr_exZ (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ) (V : (c.F →+* ℂ) → HSp D)
    (dict : ∀ σ, GA D (V σ) → Σ k, Frame ((U σ).X k).Ψ r) (hU : ∀ σ, GoodEmb c σ → IsUnf (U σ)) {G G' : WTZ E}
    (h : exZ Dw G = exZ Dw G') :
    (GoodW U x V dict G ↔ GoodW U x V dict G') ∧ rankW U G = rankW U G' ∧
      slopeW_sq U x V dict G = slopeW_sq U x V dict G' := by
  have hC : cuspW Xo c U G = cuspW Xo c U G' := by
    ext f
    rw [mem_cuspW, mem_cuspW, h]
    exact and_congr_right fun _ => forall₂_congr fun σ hσ => by rw [modelWt_congr (U σ) hσ (hU σ hσ) h]
  have hP : petW U x V dict G = petW U x V dict G' := by
    funext σ f
    unfold petW petAt
    rw [lieFacZ_congr x h, modelWt_congr (U (goodOf c σ)) (goodEmb_goodOf c σ) (hU _ (goodEmb_goodOf c σ)) h]
  exact lat_congr hC hP

end Congr

section Weights

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (Dw : Datum H)
  (a : (E →+* ℂ) × ℕ → ℕ)

theorem exZ_shift_neg (m kc : ℕ) (c0 : ℤ) :
    exZ Dw (shiftG Dw a (2 * m) (-c0)) =
      exZ Dw (wtOf Dw (uMinus Dw a (2 * m) kc c0 + parWt Dw (anchor Dw a (2 * m) kc)) ((0 : ℤ) + (m : ℤ))) := by
  rw [Model.exZ_shiftG, zero_add, exOf]
  congr 2
  simp only [uMinus, uWt, neg_smul]
  abel

end Weights

end GlobalTheory.FlatSplit

namespace GlobalTheory.FlatSplit

theorem twice_twist_ge {ι : Type} [Fintype ι] (w c1v : ι → ℝ) (pq q large₂ L b E mT CA lr m0 fr nV lS : ℝ)
    (hc1 : ∀ τ, |c1v τ + pq / 2 * large₂| ≤ 3 * q * L) (hA1 : |mT - ∑ τ, pq * w τ * large₂| ≤ CA * E)
    (hA2 : (∑ τ, |w τ|) * q * L ≤ CA * E) (hq : 0 ≤ q) (hlr : lr ≤ 2 * L) (hL : 10 ≤ L) (hm : 2 * m0 ≤ nV)
    (hm0 : 0 ≤ m0) (hfr : 0 ≤ fr) (hb : fr * nV * L ≤ b) (hbE : b ≤ E) (hLE : L ≤ E) (hlS : lS ≤ 40 * L) :
    -mT - (11 * CA + 83) * E ≤
      2 * ((∑ τ, w τ * c1v τ) - q * lr * (∑ τ, |w τ|) - m0 * fr * (Real.log (2 * Real.pi) / 2 + lr) - lS) := by
  have e1 : ∀ τ ∈ Finset.univ, (-1 / 2) * (pq * w τ * large₂) - (3 * q * L) * |w τ| ≤ w τ * c1v τ := by
    intro τ _
    have h1 : |w τ * (c1v τ + pq / 2 * large₂)| ≤ |w τ| * (3 * q * L) := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hc1 τ) (abs_nonneg _)
    have h2 := neg_abs_le (w τ * (c1v τ + pq / 2 * large₂))
    have h3 : w τ * c1v τ = w τ * (c1v τ + pq / 2 * large₂) - pq * w τ * large₂ / 2 := by ring
    linarith
  have e2 := Finset.sum_le_sum e1
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at e2
  have hS2 : 0 ≤ ∑ τ, |w τ| := Finset.sum_nonneg fun τ _ => abs_nonneg _
  have a1 := (abs_le.1 hA1).1
  have a2 : q * lr * (∑ τ, |w τ|) ≤ q * (2 * L) * (∑ τ, |w τ|) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlr hq) hS2
  have hpi : Real.log (2 * Real.pi) ≤ 2 * Real.pi - 1 := Real.log_le_sub_one_of_pos (by positivity)
  have hpi4 := Real.pi_le_four
  have a3 : Real.log (2 * Real.pi) / 2 + lr ≤ 3 * L := by linarith
  have a4 : m0 * fr * (Real.log (2 * Real.pi) / 2 + lr) ≤ m0 * fr * (3 * L) :=
    mul_le_mul_of_nonneg_left a3 (mul_nonneg hm0 hfr)
  have a5 : 2 * m0 * (fr * (3 * L)) ≤ nV * (fr * (3 * L)) :=
    mul_le_mul_of_nonneg_right hm (mul_nonneg hfr (by linarith))
  nlinarith

end GlobalTheory.FlatSplit

namespace GlobalTheory.FlatSplit

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ}

theorem lrd_le {PP A M : ℝ} (hH : HostNum D L PP A M) : GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects.lrd D.host.E ≤ 2 * L.sc.L := by
  have hd : (0 : ℝ) < |(discr D.host.E : ℝ)| := abs_pos.2 (by exact_mod_cast discr_ne_zero D.host.E)
  have hf : (8 : ℝ) ≤ D.R.f := by exact_mod_cast hH.f8
  have h1 := hH.disc
  unfold GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects.lrd
  rw [rootDiscr_def]
  push_cast
  rw [Real.log_rpow hd, hH.deg]
  push_cast
  rw [inv_mul_le_iff₀ (by positivity)]
  nlinarith

theorem flatAt_of (p : PtAt ex Csz) (i : Fin D.R.m) (Y : Cov p i) (hY : GoodCov p i Y) (hP : Hypotheses2)
    (hDG : DeepGoodAt p i Y)
    (hc : GlobalTheory.IndefiniteRowSideFullHecke.ComponentMassSum.IsComplexData Y.U (fun _ => D.sp.W ((i : ℕ) + 1)) Y.dict ∧ (∀ q : ℕ, q.Prime → Y.d.l₂.GoodAt q) ∧
      FlatExists Y.U (xiR D) ∧
      (∀ τ, |c1 Y.U (xiR D) τ + (((dat p i).p : ℝ) - (dat p i).q) / 2 * (ofRecord D L p.Del p.h0).logOm| ≤
        3 * (dat p i).q * L.sc.L) ∧
      logSum (badPrimes p.T.Q.H Y.d.l₂) ≤ 40 * L.sc.L)
    {CA PP PP' A : ℝ} (hA : AnchorAt p i CA) (hW : WtNum p i PP) (hH : HostNum D L PP' A 0) :
    FlatAt p i Y (11 * CA + 83) := by
  obtain ⟨hcx, hgood, hflat, hc1, hlog⟩ := hc
  have hj : InR D ((i : ℕ) + 1) := ⟨by omega, by have := i.2; omega⟩
  have hUn := GlobalTheory.T.unramified_points_deep_level hP D p.T ((i : ℕ) + 1) Y _ _ p.fw.laws hj hY.1
  have hrank : 1 ≤ (dat p i).p + (dat p i).q := Inhab.rank_pos p.T.toCore p.fw.laws.pins ((i : ℕ) + 1) hj
  have hev : Even (p.κ i).n := hW.dom.2
  have hFL := ((GlobalTheory.T.flatLine_thetaRoot_twist_twistingSection hP.p5 D p.T.Q.H (dat p i) Y.d.l₂ Y.d.Xo₂ Y.d.c₂ D.R.r Y.U (fun _ => D.sp.W ((i : ℕ) + 1))
    Y.dict hcx hY.1.geo hrank hgood hflat hUn (anchor (dat p i) (wtA (p.κ i)) (p.κ i).n (D.R.k - 1))
    ((p.κ i).n / 2)).2 (uM p i) 0).2 hDG.2.2.2.1
  obtain ⟨-, hrk, hdeg⟩ := hFL
  have hex : exZ (dat p i) (Gs p i (-(cZero D ((i : ℕ) + 1)))) = exZ (dat p i)
      (wtOf (dat p i) (uM p i + parWt (dat p i) (anchor (dat p i) (wtA (p.κ i)) (p.κ i).n (D.R.k - 1)))
        ((0 : ℤ) + (((p.κ i).n / 2 : ℕ) : ℤ))) := by
    have := exZ_shift_neg (dat p i) (wtA (p.κ i)) ((p.κ i).n / 2) (D.R.k - 1) (cZero D ((i : ℕ) + 1))
    rwa [Nat.two_mul_div_two_of_even hev] at this
  have hcg := congr_exZ Y.U (xiR D) (fun _ => D.sp.W ((i : ℕ) + 1)) Y.dict hY.1.unf hex
  have hR0 := hDG.2.2.2.2.1
  unfold FlatAt
  have e1 : Y.mu (Gs p i (-(cZero D ((i : ℕ) + 1)))) = slopeW_sq Y.U (xiR D) (fun _ => D.sp.W ((i : ℕ) + 1)) Y.dict
      (wtOf (dat p i) (uM p i + parWt (dat p i) (anchor (dat p i) (wtA (p.κ i)) (p.κ i).n (D.R.k - 1)))
        ((0 : ℤ) + (((p.κ i).n / 2 : ℕ) : ℤ))) := hcg.2.2
  have e2 : Y.rk (Gs p i (-(cZero D ((i : ℕ) + 1)))) = rankW Y.U (wtOf (dat p i) (uM p i) 0) := hcg.2.1.trans hrk
  have hR : (0 : ℝ) < (rankW Y.U (wtOf (dat p i) (uM p i) 0) : ℝ) := by rw [← e2]; exact_mod_cast hR0
  rw [degW_eq, degW_eq, hrk] at hdeg
  rw [e1]
  have hb1 : 1 ≤ L.sc.b := by have := hH.room; rwa [Real.rpow_zero] at this
  have hf8 : (8 : ℝ) ≤ D.R.f := by exact_mod_cast hH.f8
  have hm2 : (2 : ℝ) ≤ D.R.m := by exact_mod_cast D.R.two_le_m
  have hL := hH.big.2.1
  have hll := hH.big.2.2.2
  have k1 : (1 : ℝ) ≤ D.R.f * D.R.m := by nlinarith
  have k2 : (1 : ℝ) ≤ D.R.f * D.R.m * L.sc.L := by nlinarith
  have k3 : (1 : ℝ) ≤ D.R.f * D.R.m * L.sc.L * Real.log (Real.log L.sc.x) := by nlinarith
  have k4 : (1 : ℝ) ≤ D.R.f * D.R.m * L.sc.b * Real.log (Real.log L.sc.x) := by nlinarith
  have hbE : L.sc.b ≤ unitE p := by
    rw [hW.unit]; nlinarith [mul_le_mul_of_nonneg_left k3 (by linarith : (0 : ℝ) ≤ L.sc.b)]
  have hLE : L.sc.L ≤ unitE p := by
    rw [hW.unit]; nlinarith [mul_le_mul_of_nonneg_left k4 (by linarith : (0 : ℝ) ≤ L.sc.L)]
  have hfr : (((Module.finrank ℚ D.host.E / 2 * ((dat p i).p + (dat p i).q) : ℕ) : ℝ)) = (D.R.f : ℝ) * D.R.r := by
    rw [hH.deg, hW.sig.2.2, Nat.mul_div_cancel_left _ (by norm_num)]; push_cast; ring
  have hm : 2 * ((((p.κ i).n / 2 : ℕ) : ℝ)) ≤ (D.R.nV : ℝ) := by
    have := Nat.mul_div_le (p.κ i).n 2
    rw [hW.cols] at this
    rw [hW.cols]; exact_mod_cast (by omega : 2 * (D.R.nV / 2) ≤ D.R.nV)
  have num := twice_twist_ge (fun τ => (anchor (dat p i) (wtA (p.κ i)) (p.κ i).n (D.R.k - 1) τ : ℝ)) (c1 Y.U (xiR D))
    (((dat p i).p : ℝ) - (dat p i).q) ((dat p i).q : ℝ) (ofRecord D L p.Del p.h0).logOm L.sc.L L.sc.b (unitE p) (mainT p i) CA
    (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects.lrd D.host.E) ((((p.κ i).n / 2 : ℕ) : ℝ))
    (((Module.finrank ℚ D.host.E / 2 * ((dat p i).p + (dat p i).q) : ℕ) : ℝ)) (D.R.nV : ℝ)
    (logSum (badPrimes p.T.Q.H Y.d.l₂)) hc1 hA.1 hA.2.1 (Nat.cast_nonneg _) (lrd_le hH) hL hm (Nat.cast_nonneg _)
    (Nat.cast_nonneg _) (by rw [hfr]; exact hA.2.2) hbE hLE hlog
  rw [← mul_add] at hdeg
  have key := le_of_mul_le_mul_left hdeg hR
  show slopeW_sq Y.U (xiR D) (fun _ => D.sp.W ((i : ℕ) + 1)) Y.dict (wtOf (dat p i) (uM p i) 0) - mainT p i -
    (11 * CA + 83) * unitE p ≤ _
  linarith

end GlobalTheory.FlatSplit

namespace GlobalTheory.FlatSplit

theorem flat : Hypotheses2 → DeepGood → FlatDeg → Anchor → Flat := by
  intro hP hDG hFD hA
  refine Closed.imp (Closed.and (Closed.and (Closed.and (Closed.and hDG (GlobalTheory.T.flat_line_c1_log_bound hFD)) hA) GlobalTheory.T.weight_bound_holds)
    (GlobalTheory.CovTop.Sizes.hostN 0)) ?_
  rintro eps Fm CH - ⟨⟨⟨⟨⟨C1, -, h1⟩, ⟨C2, -, h2⟩⟩, ⟨CA, hCA, h3⟩⟩, ⟨C4, -, h4⟩⟩, ⟨C5, -, h5⟩⟩
  refine ⟨11 * CA + 83, by positivity, ?_⟩
  obtain ⟨x0, hx⟩ := (((h1.and h2).and h3).and h4).and h5
  refine ⟨x0, fun x hx' hle ι p hp i hi Y hY => ?_⟩
  obtain ⟨⟨⟨⟨a1, a2⟩, a3⟩, a4⟩, a5⟩ := hx x hx' hle ι p hp
  exact flatAt_of p i Y hY hP (a1 i hi Y hY) (a2 i hi Y hY) (a3 i) (a4 i) (a5 i)

end GlobalTheory.FlatSplit
