import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.QuoIff
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.HtValOnSubset
import Development.AbelianVarietyTheory.Definitions.Divisors.UnifOfSpaceEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SupremumConstantLogBoundStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeanLogSupNormLossLeLinearInWeightStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalLevelLiftModuliLawsOfCore
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KroneckerCharacterFrameThirdStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HostBoundHolds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightBoundHoldsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogPeriodEqKroneckerCharacterLogPeriodOfHostStatement

set_option synthInstance.maxHeartbeats 400000

noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR.Links ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop

namespace GlobalTheory.CovTop.LamCore

theorem absA_le {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (Dw : Datum H)
    (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) {B : ℝ} (hB : 0 ≤ B) (h : ∀ τ k, |(laOf Dw a n τ k : ℝ)| ≤ B) :
    ((GlobalTheory.LevGeo.absA Dw a : ℕ) : ℝ) ≤ (Module.finrank ℚ E : ℝ) * (((Dw.p + Dw.q : ℕ) : ℝ) * B) := by
  have hn : (0 : ℝ) ≤ ((n / 2 : ℕ) : ℝ) := Nat.cast_nonneg _
  have key : ∀ (b : E →+* ℂ) (i : ℕ), i < Dw.mult b → (a (b, i) : ℝ) ≤ B := by
    intro b i hi
    by_cases hb : b (H.rt : E) = H.rt0
    · have hp : i < Dw.p := by simpa [Datum.mult, hb] using hi
      have := h ⟨b, hb⟩ ⟨i, by omega⟩
      simp only [laOf, weightOf, if_pos hp, Int.cast_add, Int.cast_natCast] at this
      linarith [le_abs_self ((a (b, i) : ℝ) + ((n / 2 : ℕ) : ℝ))]
    · have hq : i < Dw.q := by simpa [Datum.mult, hb] using hi
      have := h ⟨conjEmb b, conj_mem hb⟩ ⟨Dw.p + (Dw.q - 1 - i), by omega⟩
      have e1 : ¬ (Dw.p + (Dw.q - 1 - i) < Dw.p) := by omega
      have e2 : Dw.q - 1 - (Dw.p + (Dw.q - 1 - i) - Dw.p) = i := by omega
      simp only [laOf, weightOf, if_neg e1, e2, conjEmb_conjEmb, Int.cast_sub, Int.cast_neg, Int.cast_natCast] at this
      linarith [neg_abs_le (-(a (b, i) : ℝ) - ((n / 2 : ℕ) : ℝ))]
  unfold GlobalTheory.LevGeo.absA
  rw [Nat.cast_sum, ← NumberField.Embeddings.card E ℂ, ← nsmul_eq_mul, ← Finset.card_univ]
  refine Finset.sum_le_card_nsmul _ _ _ fun b _ => ?_
  rw [Nat.cast_sum]
  refine (Finset.sum_le_card_nsmul _ _ B fun (i : Fin (Dw.mult b)) _ => key b (i : Fin (Dw.mult b)) i.2).trans ?_
  rw [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  refine mul_le_mul_of_nonneg_right ?_ hB
  have : Dw.mult b ≤ Dw.p + Dw.q := by unfold Datum.mult; split_ifs <;> omega
  exact_mod_cast this

theorem collect {f r q L b X x Om w lam sc rd : ℝ} (hf : 8 ≤ f) (hr : 1 ≤ r) (hq0 : 0 ≤ q) (hq : q ≤ r) (hL : 10 ≤ L)
    (hLx : L ≤ x) (hb : 1 ≤ b) (hZ : f * r * L ≤ X) (hOm : |Om| ≤ 3 * L) (hw0 : 0 ≤ w) (hw : w ≤ 10 * (f * r) * b)
    (h1 : lam ≤ ((1 + |Om|) / 2 + 2 * L + (2 * q + 1) * (6 * f + 48) * (2 * L)) * w)
    (h2 : sc ≤ 250 * f ^ 2 * r ^ 2 * (2 * L)) (h3 : rd ≤ 217 * (f * r * L) ^ 2) :
    2 * lam + 2 * sc + rd ≤ x ^ 4 * X ^ 2 * b := by
  have hfr : 1 ≤ f * r := by nlinarith
  have hZ0 : L ≤ f * r * L := by nlinarith
  have hfrX : f * r ≤ X := by nlinarith
  have hX : 1 ≤ X := hfr.trans hfrX
  have a1 : (2 * q + 1) * (6 * f + 48) ≤ (3 * r) * (12 * f) :=
    mul_le_mul (by linarith) (by linarith) (by linarith) (by linarith)
  have a2 : (2 * q + 1) * (6 * f + 48) * (2 * L) ≤ 72 * (f * r * L) := by nlinarith
  have a3 : (1 + |Om|) / 2 + 2 * L + (2 * q + 1) * (6 * f + 48) * (2 * L) ≤ 76 * X := by linarith
  have a4 : w ≤ 10 * X * b := hw.trans (by gcongr)
  have a5 : lam ≤ 76 * X * (10 * X * b) := h1.trans (mul_le_mul a3 a4 hw0 (by positivity))
  have a6 : (f * r * L) ^ 2 ≤ X ^ 2 := pow_le_pow_left₀ (by linarith) hZ 2
  have a7 : (f * r) * (f * r * L) ≤ X * X := mul_le_mul hfrX hZ (by linarith) (by linarith)
  have a8 : X ^ 2 ≤ X ^ 2 * b := le_mul_of_one_le_right (by positivity) hb
  have a9 : (10 : ℝ) ^ 4 ≤ x ^ 4 := pow_le_pow_left₀ (by norm_num) (hL.trans hLx) 4
  have a10 : 10 ^ 4 * (X ^ 2 * b) ≤ x ^ 4 * (X ^ 2 * b) := mul_le_mul_of_nonneg_right a9 (by positivity)
  have a11 : 0 ≤ X ^ 2 * b := by positivity
  nlinarith

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m)

theorem ne_bot_of_form {K K' R W : Type} [Field K] [NumberField K] [Field K'] [AddCommGroup R] [Module K R] [AddCommGroup W]
    [Module K W] [Module K' W] {C C' : Submodule K R} (hC : C' = C) [Module (𝓞 K) C'] {M : Submodule (𝓞 K) C'}
    (hs : Submodule.span K (M : Set C') = ⊤) {WK : Submodule K W} (e : C ≃ₗ[K] WK) {n : ℕ} {b : Fin n → W} (hb : ∀ k, b k ∈ WK)
    (hsp : Submodule.span K' (Set.range b) = ⊤) {y : W} (hy : y ≠ 0) : M ≠ ⊥ := by
  subst hC
  rintro rfl
  rw [Submodule.bot_coe, Submodule.span_zero_singleton] at hs
  have h3 : ∀ k, b k = 0 := fun k => by
    have h1 : e.symm ⟨b k, hb k⟩ ∈ (⊥ : Submodule K C') := by rw [hs]; exact Submodule.mem_top
    rw [Submodule.mem_bot, LinearEquiv.map_eq_zero_iff] at h1
    exact congrArg Subtype.val h1
  have h4 : Submodule.span K' (Set.range b) ≤ ⊥ := Submodule.span_le.2 (by rintro _ ⟨k, rfl⟩; exact h3 k)
  exact hy (h4 (by rw [hsp]; exact Submodule.mem_top))

set_option maxHeartbeats 1000000 in

theorem latW_ne_bot (h : GramAt p i) : latW (p.T.U ((i : ℕ) + 1)) (Gk p i) ≠ ⊥ := by
  obtain ⟨-, -, hg, -, -, hs⟩ := h
  obtain ⟨y, -, hy⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hg
  obtain ⟨n, b, hb, -, -, -, hsp⟩ := p.fw.ks i
  exact ne_bot_of_form (cuspW_wtZ _ _) hs (p.fw.e i) hb hsp hy

set_option maxHeartbeats 1000000 in

theorem slopeMax_le (h6 : GlobalTheory.Published.TamagawaSpecialUnitary) {PP A : ℝ} (hR : RecTied D L) (hG : GramAt p i)
    (hN : HostNum D L PP A 1) (hW : WtNum p i PP) :
    slopeMax_sq (nrmK p.fw i) (latW (p.T.U ((i : ℕ) + 1)) (Gk p i)) ≤ L.sc.x ^ (2 * A + 4) * L.sc.b := by
  have hj : Formalism.L2.Pj.InR D ((i : ℕ) + 1) := ⟨by omega, i.2⟩
  obtain ⟨hLaws, hnorm⟩ := GlobalTheory.LevGeo.laws_of_coreJ D p.T _ p.fw.laws hj
  have hn : normW (p.T.U ((i : ℕ) + 1)) (xiR D) (fun _ => D.sp.W ((i : ℕ) + 1)) (GlobalTheory.LevGeo.coreDict p.T.toCore ((i : ℕ) + 1))
      (Gk p i) = nrmK p.fw i := by
    funext σ f; exact hnorm _ σ f
  obtain ⟨_, χ, hχ, hOm, -, -⟩ := GlobalTheory.T.logPeriod_eq_kroneckerCharacter_logPeriod_of_host D L p.T.Q p.fw.laws.pins.1 p.Del p.h0
  have hgood : GoodW (p.T.U ((i : ℕ) + 1)) (xiR D) (fun _ => D.sp.W ((i : ℕ) + 1))
      (GlobalTheory.LevGeo.coreDict p.T.toCore ((i : ℕ) + 1)) (Gk p i) := ⟨by rw [hn]; exact hG.2.2.2.1, hG.2.2.2.2⟩
  have main := GlobalTheory.T.kronecker_character_frame_third h6 D _ _ _ _ _ _ _ _ hLaws χ hχ (wtA (p.κ i)) (p.κ i).n hW.dom hgood (latW_ne_bot p i hG)
  rw [hn] at main
  refine main.trans ?_
  rw [hOm, p.fw.laws.pins.2.1.1, hW.cols]
  obtain ⟨-, hL, hLx, -⟩ := hN.big
  have hfd : fdeg D.host.E = D.R.f := by unfold fdeg; rw [hN.deg]; omega
  have hf : (8 : ℝ) ≤ D.R.f := by exact_mod_cast hN.f8
  have hr2 : 2 ≤ D.R.r := by
    have h1 := D.R.two_le_m
    have h2 := D.R.m_add_three_le_k
    unfold Ranks.r; omega
  have hr : (1 : ℝ) ≤ D.R.r := by exact_mod_cast (by omega : 1 ≤ D.R.r)
  have hnV : (1 : ℝ) ≤ D.R.nV := by exact_mod_cast (by unfold Ranks.nV; omega : 1 ≤ D.R.nV)
  have hbL : L.sc.b = Real.exp L.sc.L := rfl
  have hb : 1 ≤ L.sc.b := by rw [hbL]; exact Real.one_le_exp (by linarith)
  have hx0 : 0 < L.sc.x := by linarith
  have hXb : L.sc.x ^ A ≤ L.sc.b := by simpa using hN.room
  have hP := hN.poly.2.2
  have hfr : (1 : ℝ) ≤ (D.R.f : ℝ) * D.R.r := by nlinarith
  have hZ : (D.R.f : ℝ) * D.R.r * L.sc.L ≤ L.sc.x ^ A :=
    le_trans (mul_le_mul_of_nonneg_right (le_mul_of_one_le_right (by positivity) hnV) (by linarith)) hP
  have ht : ((fdeg D.host.E * D.R.r * D.R.nV : ℕ) : ℝ) ≤ L.sc.b := by
    rw [hfd]; push_cast
    exact (le_mul_of_one_le_right (by positivity) (by linarith)).trans (hP.trans hXb)
  have hs : ((GlobalTheory.LevGeo.absA (dat p i) (wtA (p.κ i)) : ℕ) : ℝ) ≤ 8 * ((D.R.f : ℝ) * D.R.r) * L.sc.b := by
    have := absA_le (dat p i) (wtA (p.κ i)) (p.κ i).n (by positivity) hW.up
    rw [hW.sig.2.2, hN.deg] at this
    push_cast at this
    linarith
  have hs0 : (0 : ℝ) ≤ ((GlobalTheory.LevGeo.absA (dat p i) (wtA (p.κ i)) : ℕ) : ℝ) := Nat.cast_nonneg _
  have ht0 : (0 : ℝ) ≤ ((fdeg D.host.E * D.R.r * D.R.nV : ℕ) : ℝ) := Nat.cast_nonneg _
  generalize ((GlobalTheory.LevGeo.absA (dat p i) (wtA (p.κ i)) : ℕ) : ℝ) = s at *
  generalize ((fdeg D.host.E * D.R.r * D.R.nV : ℕ) : ℝ) = t at *
  have hbb : L.sc.b ≤ (D.R.f : ℝ) * D.R.r * L.sc.b := le_mul_of_one_le_left (by linarith) hfr
  have hw : s + t + 1 ≤ 10 * ((D.R.f : ℝ) * D.R.r) * L.sc.b := by linarith
  have hlw : Real.log (s + t + 1) ≤ 2 * (2 * L.sc.L) := by
    refine (Real.log_le_log (by linarith) hw).trans ?_
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by norm_num) (by positivity), hbL, Real.log_exp]
    linarith [hN.logfr.1, Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 10)]
  have hg : ∀ k, 0 < D.host.g k := fun k => (D.host.g_prime k).pos
  have hM : 1 ≤ D.host.g 0 * D.host.g 1 := Nat.mul_pos (hg 0) (hg 1)
  have hlM : Real.log ((D.host.g 0 * D.host.g 1 : ℕ) : ℝ) ≤ 30 * (2 * L.sc.L) := by
    push_cast
    rw [Real.log_mul (by exact_mod_cast (hg 0).ne') (by exact_mod_cast (hg 1).ne')]
    linarith [hN.logg 0, hN.logg 1]
  have hd : 1 ≤ D.host.d := by rw [← p.fw.laws.pins.1.1]; exact p.T.Q.H.d_prime.pos
  have hl1 : Real.log ((fdeg D.host.E : ℝ) * D.R.r) ≤ 2 * L.sc.L := by rw [hfd]; linarith [hN.logfr.1]
  have hl2 : Real.log (dE D.host.E) ≤ 4 * (fdeg D.host.E : ℝ) * (2 * L.sc.L) := by
    rw [hfd]; unfold dE
    have : 0 ≤ (D.R.f : ℝ) * L.sc.L := by positivity
    linarith [hN.disc]
  have hl3 : Real.log (D.host.d : ℝ) ≤ 4 * (2 * L.sc.L) := by linarith [hN.logd]
  have n1 := (GlobalTheory.T.supremum_constant_log_bound D.host.E D.R.r D.host.d _ (s + t + 1) (2 * L.sc.L) hr2 hd hM (by linarith) (by linarith)
    hl1 hlM hl2 hl3 hlw).2
  have n2 := GlobalTheory.T.meanLogSupNormLoss_le_linear_in_weight D.host.E D.R.r (dat p i).q D.host.d _ (ofRecord D L p.Del p.h0).logOm s t (2 * L.sc.L) (by omega) hd hM
    (by linarith) hs0 ht0 hl1 hlM hl2 hl3 hlw
  have n3 := (log_rd_le_fieldSz _).trans (hR.core_size_le p (by linarith))
  rw [hfd] at n1 n2
  have hq : ((dat p i).q : ℝ) ≤ D.R.r := by exact_mod_cast (by have := hW.sig.2.2; omega : (dat p i).q ≤ D.R.r)
  have e : L.sc.x ^ (2 * A + 4) = L.sc.x ^ 4 * (L.sc.x ^ A) ^ 2 := by
    rw [Real.rpow_add hx0, mul_comm 2 A, Real.rpow_mul hx0.le, mul_comm]
    norm_cast
  rw [e]
  exact collect hf hr (Nat.cast_nonneg _) hq hL hLx hb hZ hW.om (add_nonneg hs0 ht0) (by linarith) n2 n1 n3

theorem lamCore : Hypotheses2 → Gram → Lifts fun Fm x _ ι p i _ A =>
    slopeMax_sq (nrmK p.fw i) (latW (p.T.U ((i : ℕ) + 1)) (Gk p i)) ≤ (Fm.L x ι).sc.x ^ A * (Fm.L x ι).sc.b := by
  intro hP hG
  refine Closed.imp (Closed.and hG (Closed.and (GlobalTheory.CovTop.Sizes.hostN 1) GlobalTheory.T.weight_bound_holds)) ?_
  rintro eps Fm CH - ⟨⟨_, -, h1⟩, ⟨A, hA, h2⟩, ⟨_, -, h3⟩⟩
  obtain ⟨x0, h⟩ := h1.and (h2.and h3)
  refine ⟨2 * A + 4, by linarith, x0, fun x hx hle ι p hp i => ?_⟩
  obtain ⟨a, b, c⟩ := h x hx hle ι p hp
  exact slopeMax_le p i hP.p6 hp.2 (a i) (b i) (c i)

end GlobalTheory.CovTop.LamCore

end
