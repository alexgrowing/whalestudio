import Formalism.HermitianCurvature.StatementPN
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LocalVolumePositivity

namespace Formalism.FourierDecayAlt.P.HermitianFormNormLemmas.A

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.PN

section

open Finset
open Formalism.FourierDecayAlt

theorem book_constants_pos_of_pos {P : Type} [Fintype P] (B : S3.MassData P) (h : B.Pos) :
    0 < B.Gam1 ∧ 0 < B.μK ∧ 0 < B.μKpp ∧ 0 < B.μSpp ∧ 0 < B.μSpp' ∧ 0 < B.MM ∧ 0 < B.unitLevelVolume ∧
    0 < B.c0 ∧ 0 < B.c0' ∧ 0 < B.tt ∧ 0 < B.AA ∧ 0 < B.Dstar := by
  obtain ⟨hp, hKo, hSo, hSo', hMo, hU00o, hμH, hμH', hHpp, hHpp', hμN, hμN', hZZ, hPP, hal, hG, hHa, hHa',
    hNa, hNa', hB, hVH, hVH', hVN, hVN', hCoo, hdeg, hdimπ, hdimπ', hρ0, hρ0', hd, hd', hn0c, hsup, hδ⟩ := h
  have hg : ∀ p, 0 < B.g p := fun p => (hp p).1
  have hglk : ∀ p, 0 < B.glk p := fun p => (hp p).2.1
  have huk : ∀ p, 0 < B.uk p := fun p => (hp p).2.2.1
  have hKp : ∀ p, 0 < B.μKp p := fun p => (hp p).2.2.2.2.2.1
  have hKppp : ∀ p, 0 < B.μKppp p := fun p => (hp p).2.2.2.2.2.2.2.1
  have hSppp : ∀ p, 0 < B.μSppp p := fun p => (hp p).2.2.2.2.2.2.2.2.2.2.1
  have hSppp' : ∀ p, 0 < B.μSppp' p := fun p => (hp p).2.2.2.2.2.2.2.2.2.2.2.1
  have hMp : ∀ p, 0 < B.Mp p := fun p => (hp p).2.2.2.2.2.2.2.2.2.2.2.2.1
  have hU00p : ∀ p, 0 < B.localVolumeAtPlace p := fun p => (hp p).2.2.2.2.2.2.2.2.2.2.2.2.2
  have hμK : 0 < B.μK := show 0 < B.μKo * ∏ p, B.μKp p from mul_pos hKo (Finset.prod_pos fun p _ => hKp p)
  have hμKpp : 0 < B.μKpp := show 0 < B.μKo * ∏ p, B.μKppp p from
    mul_pos hKo (Finset.prod_pos fun p _ => hKppp p)
  have hMM : 0 < B.MM := show 0 < B.Mo * ∏ p, B.Mp p from mul_pos hMo (Finset.prod_pos fun p _ => hMp p)
  refine ⟨?_, hμK, hμKpp, ?_, ?_, hMM, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show 0 < ∏ p, B.glk p / B.uk p
    exact Finset.prod_pos fun p _ => div_pos (hglk p) (huk p)
  · show 0 < B.μSo * ∏ p, B.μSppp p
    exact mul_pos hSo (Finset.prod_pos fun p _ => hSppp p)
  · show 0 < B.μSo' * ∏ p, B.μSppp' p
    exact mul_pos hSo' (Finset.prod_pos fun p _ => hSppp' p)
  · show 0 < B.localVolumeArchimedean * ∏ p, B.localVolumeAtPlace p
    exact mul_pos hU00o (Finset.prod_pos fun p _ => hU00p p)
  · show 0 < B.volN * B.volH / B.dimπ
    exact div_pos (mul_pos hVN hVH) hdimπ
  · show 0 < B.volN' * B.volH' / B.dimπ'
    exact div_pos (mul_pos hVN' hVH') hdimπ'
  · show 0 < ∏ p, (1 + 3 / B.g p)
    exact Finset.prod_pos fun p _ => by have := hg p; positivity
  · show 0 < B.volB * B.Coo * (B.MM / B.volZZ) / B.μK
    exact div_pos (mul_pos (mul_pos hB hCoo) (div_pos hMM hZZ)) hμK
  · show 0 < B.deg * (B.volG / B.μKpp)
    exact mul_pos hdeg (div_pos hG hμKpp)

theorem t_NormOfLemmas : NormOfLemmas := by
  intro hJC hLP hCo P _ B hin
  obtain ⟨hPos, hJac, hNu, hInf, hVol, hLev, hMas, hCol, hOrd, hTyp, hInd⟩ := hin
  obtain ⟨hGam, hμK, hμKpp, hμSpp, hμSpp', hMM, hU, hc0, hc0', htt, hAA, hD⟩ := book_constants_pos_of_pos B hPos
  have hJ := hJC P B hPos hJac hNu
  have hL := (hLP P B hPos hOrd hTyp hInd).1
  obtain ⟨-, -, hC1, -, -, hC2⟩ := hCo P B hPos hVol hLev hMas hCol
  have hPos' := hPos
  obtain ⟨hp, hμKo, hμSo, hμSo', hMo, hU00o, hμH, hμH', hμHpp, hμHpp', hμN, hμN', hvolZZ, hvolPP, hal,
    hvolG, hvolHa, hvolHa', hvolNa, hvolNa', hvolB, hvolH, hvolH', hvolN, hvolN', hCoo, hdeg, hdimπ,
    hdimπ', hρ0, hρ0', hd, hd', hn0c, hsup, hδ⟩ := hPos'
  have hV := hVol.1
  unfold S3.MassData.InInfinity at hInf

  have key : B.Gam1 * B.AA * ((B.c0 * B.c0')⁻¹ * (B.volZZ / B.unitLevelVolume * B.Coo⁻¹)) * (1 / B.deg)
      = B.d * B.d' / B.Dstar := by
    have e1 : B.Gam1 * B.AA * ((B.c0 * B.c0')⁻¹ * (B.volZZ / B.unitLevelVolume * B.Coo⁻¹))
        = B.Gam1 * B.volB * (B.MM / B.unitLevelVolume / B.μK) * ((1 / B.c0) * (1 / B.c0')) := by
      unfold S3.MassData.AA
      field_simp
    rw [e1, hL, hC1, hC2]
    unfold S3.MassData.Dstar
    have hVG : B.volG = B.volHa * B.volHa' / B.volB := by
      field_simp
      linarith
    rw [hVG]
    field_simp
  have hX : 0 ≤ B.Gam1 * B.AA * ((B.c0 * B.c0')⁻¹ * (B.volZZ / B.unitLevelVolume * B.Coo⁻¹)) := by
    positivity
  calc B.Gam1 * B.AA * ((B.c0 * B.c0')⁻¹ * B.IntN)
      = B.Gam1 * B.AA * ((B.c0 * B.c0')⁻¹ * (B.volZZ / B.unitLevelVolume * B.Coo⁻¹)) * B.IntOO := by
        rw [hJ]; ring
    _ ≤ B.Gam1 * B.AA * ((B.c0 * B.c0')⁻¹ * (B.volZZ / B.unitLevelVolume * B.Coo⁻¹)) * (1 / B.deg) :=
        mul_le_mul_of_nonneg_left hInf hX
    _ = B.d * B.d' / B.Dstar := key

theorem t_FramePassage : FramePassage := by
  intro P _ B rd g r k f Irat Ire hPos hJac hFr
  obtain ⟨hrd, hg, F1, F2, F3⟩ := hFr
  obtain ⟨hGam, hμK, hμKpp, hμSpp, hμSpp', hMM, hU, hc0, hc0', htt, hAA, hD⟩ := book_constants_pos_of_pos B hPos
  have hvolZZ : 0 < B.volZZ := hPos.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hvolPP : 0 < B.volPP := hPos.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  unfold S3.MassData.InJacMod at hJac
  have hexp : rd ^ (((f * (r + 1) * (8 * r ^ 2 + 10 * r + 3) : ℕ) : ℝ) / 3)
      = rd ^ (f * (r + 1)) * rd ^ (((f * r * (r + 1) * (8 * r + 10) : ℕ) : ℝ) / 3) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hrd]
    congr 1
    push_cast
    ring
  have h1 : (B.c0 * B.c0')⁻¹ * B.IntN = (B.unitLevelVolume / B.volZZ)⁻¹ * ((B.c0 * B.c0')⁻¹ * B.IntC) := by
    rw [hJac]
    field_simp
  have hpb : 0 < rd ^ (((f * r * (r + 1) * (8 * r + 10) : ℕ) : ℝ) / 3) := Real.rpow_pos_of_pos hrd _
  rw [h1, F1, F2, F3, hexp, div_pow]
  have h2 : (0 : ℝ) < 2 ^ (f * (r + 1)) := by positivity
  have h3 : 0 < rd ^ (f * (r + 1)) := by positivity
  have h4 : 0 < g ^ (f * (r + 1) * (2 * r + 3)) := by positivity
  field_simp

theorem t_NormRe : NormRe := by
  intro hN hF P _ B rd g r k f Irat Ire hin hFr
  have h1 := hN P B hin
  have h2 := hF P B rd g r k f Irat Ire hin.1 hin.2.1 hFr
  obtain ⟨hrd, hg, -, -, -⟩ := hFr
  have hvg : 0 ≤ (rd / 2) ^ (f * (r + 1)) * g ^ (f * (r + 1) * (2 * r + 3)) := by positivity
  calc B.Gam1 * (abelian₂ rd r k f * B.AA) * Ire = B.Gam1 * B.AA * (abelian₂ rd r k f * Ire) := by ring
    _ = (rd / 2) ^ (f * (r + 1)) * g ^ (f * (r + 1) * (2 * r + 3)) *
          (B.Gam1 * B.AA * ((B.c0 * B.c0')⁻¹ * B.IntN)) := by rw [h2]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left h1 hvg

theorem t_NormOfMain : NormOfMain := by
  intro hM P _ B hin
  obtain ⟨hPos, hJac, hNu, hInf, hVol, hLev, hMas, hCol, hOrd, hTyp, hInd⟩ := hin
  obtain ⟨hGam, hμK, hμKpp, hμSpp, hμSpp', hMM, hU, hc0, hc0', htt, hAA, hD⟩ := book_constants_pos_of_pos B hPos
  have hPos' := hPos
  obtain ⟨hp, hμKo, hμSo, hμSo', hMo, hU00o, hμH, hμH', hμHpp, hμHpp', hμN, hμN', hvolZZ, hvolPP, hal,
    hvolG, hvolHa, hvolHa', hvolNa, hvolNa', hvolB, hvolH, hvolH', hvolN, hvolN', hCoo, hdeg, hdimπ,
    hdimπ', hρ0, hρ0', hd, hd', hn0c, hsup, hδ⟩ := hPos'
  by_cases hI : 0 ≤ B.IntN
  · let B' : S3.MassData P := { B with
      δ := 0, e1 := 1, supdens := 1, KtopV := B.IntN / (B.c0 * B.c0'), n0c := B.AA / B.ρ0,
      KV := B.AA / B.ρ0 * (B.IntN / (B.c0 * B.c0')),
      Sig := B.ρ0 * (B.AA / B.ρ0 * (B.IntN / (B.c0 * B.c0'))),
      Kgs2 := B.tt * B.Gam1 * (B.ρ0 * (B.AA / B.ρ0 * (B.IntN / (B.c0 * B.c0')))) }
    have hPosB' : B'.Pos :=
      ⟨hp, hμKo, hμSo, hμSo', hMo, hU00o, hμH, hμH', hμHpp, hμHpp', hμN, hμN', hvolZZ, hvolPP, hal,
        hvolG, hvolHa, hvolHa', hvolNa, hvolNa', hvolB, hvolH, hvolH', hvolN, hvolN', hCoo, hdeg, hdimπ,
        hdimπ', hρ0, hρ0', hd, hd', div_pos hAA hρ0, zero_le_one, le_refl 0⟩
    have hTwoA : B'.InTwoA := le_refl _
    have hForm : B'.InForm := rfl
    have hKer : B'.InKernel := by
      refine ⟨?_, div_nonneg hI (mul_pos hc0 hc0').le⟩
      show B.AA / B.ρ0 * (B.IntN / (B.c0 * B.c0')) ≤ 1 * (B.AA / B.ρ0) * (B.IntN / (B.c0 * B.c0'))
      rw [one_mul]
    have hMass : B'.InMass := by
      show B.AA / B.ρ0 * B.ρ0 = B.AA
      field_simp
    have hDens : B'.InDens := le_refl (1 : ℝ)
    have hThA : B'.InTheoremA := by
      show B.c0 * B.c0' * (B.IntN / (B.c0 * B.c0')) ≤ (1 + 0) * B.IntN
      have : B.c0 * B.c0' * (B.IntN / (B.c0 * B.c0')) = B.IntN := by field_simp
      rw [this]; simp
    obtain ⟨hGS, hB, -⟩ := hM P B' hPosB' hTwoA hForm hKer hMass hDens hThA hJac hNu hInf hVol hLev hMas
      hCol hOrd hTyp hInd
    rw [hGS] at hB
    have hB2 : B.tt * B.Gam1 * (B.ρ0 * (B.AA / B.ρ0 * (B.IntN / (B.c0 * B.c0')))) ≤
        (1 + 0) * 1 * B.tt * (B.d * B.d' / B.Dstar) := hB
    have e : B.tt * B.Gam1 * (B.ρ0 * (B.AA / B.ρ0 * (B.IntN / (B.c0 * B.c0')))) =
        B.tt * (B.Gam1 * B.AA * ((B.c0 * B.c0')⁻¹ * B.IntN)) := by field_simp
    rw [e] at hB2
    have hB3 : B.tt * (B.Gam1 * B.AA * ((B.c0 * B.c0')⁻¹ * B.IntN)) ≤ B.tt * (B.d * B.d' / B.Dstar) := by
      linarith
    exact le_of_mul_le_mul_left hB3 htt
  · have hI' : B.IntN ≤ 0 := le_of_not_ge hI
    have h1 : B.Gam1 * B.AA * ((B.c0 * B.c0')⁻¹ * B.IntN) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (mul_pos hGam hAA).le
        (mul_nonpos_of_nonneg_of_nonpos (inv_pos.mpr (mul_pos hc0 hc0')).le hI')
    have h2 : 0 ≤ B.d * B.d' / B.Dstar := (div_pos (mul_pos hd hd') hD).le
    linarith

end

end Formalism.FourierDecayAlt.P.HermitianFormNormLemmas.A

namespace Formalism.FourierDecayAlt.P.HermitianFormNormLemmas.B

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.PN

section

open Finset
open Classical

theorem t_ZpowForm : Formalism.FourierDecayAlt.PN.ZpowForm := by
  unfold Formalism.FourierDecayAlt.PN.ZpowForm
  intro q k r _ hk
  rw [zpow_neg]
  congr 1
  have e : ((k : ℤ) - 2 * r - 5) = ((k - 2 * r - 5 : ℕ) : ℤ) := by omega
  rw [e, zpow_natCast]

variable {Cl Nu : Type}

private theorem sum_le_mul_sum_of_fiber_weight_bound {X Dt : Type} [Fintype Dt] [DecidableEq Dt] (S : Finset X)
    (dat : X → Option Dt) (f w : X → ℝ) (F W : Dt → ℝ) (V : ℝ) (hF : ∀ d, 0 ≤ F d)
    (hnone : ∀ x, dat x = none → f x = 0) (hsome : ∀ x d, dat x = some d → f x = w x * F d)
    (hU : ∀ d (T : Finset X), (∀ x ∈ T, dat x = some d) → ∑ x ∈ T, w x ≤ V * W d) :
    ∑ x ∈ S, f x ≤ V * ∑ d, W d * F d := by
  rw [← Finset.sum_fiberwise S dat f, Fintype.sum_option, Finset.mul_sum]
  have h0 : ∑ x ∈ S with dat x = none, f x = 0 :=
    Finset.sum_eq_zero (fun x hx => hnone x (Finset.mem_filter.1 hx).2)
  rw [h0, zero_add]
  refine Finset.sum_le_sum (fun d _ => ?_)
  have h1 : ∑ x ∈ S with dat x = some d, f x = (∑ x ∈ S with dat x = some d, w x) * F d := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl (fun x hx => hsome x d (Finset.mem_filter.1 hx).2)
  rw [h1, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right (hU d _ (fun x hx => (Finset.mem_filter.1 hx).2)) (hF d)

theorem step1 (L : LocalNG Cl Nu) (hU : L.Unfold) (S : Finset (Cl × Nu)) :
    ∑ x ∈ S, L.a2 x.1 x.2 ≤ L.V0 * ∑ d, (∏ p, L.wt p (d p)) * ‖L.ampNG d‖ ^ 2 := by
  unfold LocalNG.Unfold at hU
  refine sum_le_mul_sum_of_fiber_weight_bound S (fun x => L.dat x.1 x.2) (fun x => L.a2 x.1 x.2) (fun x => L.rw x.1)
    (fun d => ‖L.ampNG d‖ ^ 2) (fun d => ∏ p, L.wt p (d p)) L.V0 (fun d => sq_nonneg _) ?_ ?_
    (fun d T hT => hU d T hT)
  · intro x h
    unfold LocalNG.a2
    simp only [h]
  · intro x d h
    unfold LocalNG.a2
    simp only [h]
    try rfl

theorem core (hS4 : Formalism.HermitianLatticeCounting.S4.Step4) (L : LocalNG Cl Nu) (κ : ℕ) (Xp Yp : L.P → ℝ)
    (hX : ∀ p, 1 ≤ Xp p) (hY : ∀ p, 1 ≤ Yp p) (hb : L.Basic)
    (h1 : ∀ p ∈ L.Om, ∑ d, L.wt p d * ‖L.aN p d‖ ^ 2 ≤ Xp p * ((L.q p : ℝ) ^ κ)⁻¹ * L.nn p)
    (h2 : ∀ p, ∑ d, L.wt p d * ‖L.aZ p d‖ ^ 2 ≤ Xp p * L.nn p)
    (h3 : ∀ p, L.nn p ≤ Yp p * L.ngen p) :
    ∑ d, (∏ p, L.wt p (d p)) * ‖L.ampNG d‖ ^ 2 ≤
      (4 : ℝ) ^ L.Om.card * (∏ p, Xp p * Yp p) * ((2 : ℝ) ^ κ)⁻¹ * ∏ p, L.ngen p := by
  unfold Formalism.HermitianLatticeCounting.S4.Step4 at hS4
  have hb' := hb
  unfold LocalNG.Basic at hb'
  obtain ⟨hw, _, hq, _, hnn, _, _⟩ := hb'
  have key := hS4 L.P L.Om L.D L.wt L.aN L.aZ (fun _ => 1) (fun p => Xp p * L.nn p)
    (fun p => Xp p * Yp p * L.ngen p) L.q 0 κ hw (fun _ => le_refl _) hq
    (fun p => mul_nonneg (by linarith [hX p]) (hnn p))
    (fun p hp => (h1 p hp).trans (le_of_eq (by simp only [pow_zero, one_mul]; ring)))
    (fun p => (h2 p).trans (le_of_eq (by simp only [pow_zero, one_mul])))
    (fun p => by
      simp only [pow_zero, one_mul]
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (h3 p) (by linarith [hX p]))
  refine le_trans (le_of_eq ?_) (key.trans (le_of_eq ?_))
  · unfold LocalNG.ampNG
    first
    | rfl
    | congr!
  · simp only [Finset.prod_const_one, one_pow, mul_one, Finset.prod_mul_distrib] <;> ring

theorem pow_card_eq {P : Type} [Fintype P] (Om : Finset P) (a : ℝ) :
    a ^ Om.card = ∏ p, if p ∈ Om then a else 1 := by
  rw [Finset.prod_ite_mem, Finset.univ_inter, Finset.prod_const]

theorem finish (L : LocalNG Cl Nu) (Xp Yp : L.P → ℝ) (hX : ∀ p, 1 ≤ Xp p) (hY : ∀ p, 1 ≤ Yp p) (e : ℕ)
    (h : ∀ p, (if p ∈ L.Om then (4 : ℝ) else 1) * (Xp p * Yp p) ≤ L.H p ^ e) :
    (4 : ℝ) ^ L.Om.card * (∏ p, Xp p * Yp p) ≤ L.Htot ^ e := by
  have hnn : ∀ p ∈ Finset.univ, 0 ≤ (if p ∈ L.Om then (4 : ℝ) else 1) * (Xp p * Yp p) := by
    intro p _
    exact mul_nonneg (by split_ifs <;> norm_num)
      (mul_nonneg (by linarith [hX p]) (by linarith [hY p]))
  calc (4 : ℝ) ^ L.Om.card * (∏ p, Xp p * Yp p)
      = ∏ p, (if p ∈ L.Om then (4 : ℝ) else 1) * (Xp p * Yp p) := by
        rw [pow_card_eq, ← Finset.prod_mul_distrib]
    _ ≤ ∏ p, L.H p ^ e := Finset.prod_le_prod hnn (fun p _ => h p)
    _ = L.Htot ^ e := by
        rw [Finset.prod_pow]
        rfl

theorem ngen_nonneg (L : LocalNG Cl Nu) (C0 r : ℕ) (hb : L.Basic) (hM : L.MassRatioAt C0 r) (p : L.P) :
    0 ≤ L.ngen p := by
  unfold LocalNG.Basic at hb
  unfold LocalNG.MassRatioAt at hM
  obtain ⟨_, hH, _, _, hnn, _⟩ := hb
  by_cases hp : p ∈ L.Om
  · have h1 := hM.2 p hp
    have h2 := hnn p
    have hpos : 0 < 8 * L.H p ^ (C0 * (r + 1) ^ 2 + 2 * (2 * r + 2)) :=
      mul_pos (by norm_num) (pow_pos (by linarith [hH p]) _)
    by_contra hneg
    push_neg at hneg
    have := mul_neg_of_pos_of_neg hpos hneg
    linarith
  · rw [← hM.1 p hp]
    exact hnn p

theorem two_le_H (L : LocalNG Cl Nu) (hb : L.Basic) (p : L.P) (hp : p ∈ L.Om) : 2 ≤ L.H p := by
  unfold LocalNG.Basic at hb
  obtain ⟨_, _, hq, hqH, _⟩ := hb
  have h2 : (2 : ℝ) ≤ (L.q p : ℝ) := by exact_mod_cast hq p
  exact h2.trans (hqH p hp)

theorem mean (hS4 : Formalism.HermitianLatticeCounting.S4.Step4) (L : LocalNG Cl Nu) (C0 r κ e : ℕ) (Xp Yp : L.P → ℝ)
    (hX : ∀ p, 1 ≤ Xp p) (hY : ∀ p, 1 ≤ Yp p) (hb : L.Basic) (hM : L.MassRatioAt C0 r) (hU : L.Unfold)
    (h1 : ∀ p ∈ L.Om, ∑ d, L.wt p d * ‖L.aN p d‖ ^ 2 ≤ Xp p * ((L.q p : ℝ) ^ κ)⁻¹ * L.nn p)
    (h2 : ∀ p, ∑ d, L.wt p d * ‖L.aZ p d‖ ^ 2 ≤ Xp p * L.nn p)
    (h3 : ∀ p, L.nn p ≤ Yp p * L.ngen p)
    (h : ∀ p, (if p ∈ L.Om then (4 : ℝ) else 1) * (Xp p * Yp p) ≤ L.H p ^ e) (S : Finset (Cl × Nu)) :
    ∑ x ∈ S, L.a2 x.1 x.2 ≤ ((2 : ℝ) ^ κ)⁻¹ * L.Htot ^ e * L.ngenTot := by
  have hb' := hb
  unfold LocalNG.Basic at hb'
  have hV0 : 0 ≤ L.V0 := hb'.2.2.2.2.2.1
  have hng : 0 ≤ ∏ p, L.ngen p := Finset.prod_nonneg (fun p _ => ngen_nonneg L C0 r hb hM p)
  have hfin := finish L Xp Yp hX hY e h
  have hcore := core hS4 L κ Xp Yp hX hY hb h1 h2 h3
  have hstep := step1 L hU S
  have hk : 0 ≤ ((2 : ℝ) ^ κ)⁻¹ := by positivity
  calc ∑ x ∈ S, L.a2 x.1 x.2 ≤ L.V0 * ∑ d, (∏ p, L.wt p (d p)) * ‖L.ampNG d‖ ^ 2 := hstep
    _ ≤ L.V0 * ((4 : ℝ) ^ L.Om.card * (∏ p, Xp p * Yp p) * ((2 : ℝ) ^ κ)⁻¹ * ∏ p, L.ngen p) :=
        mul_le_mul_of_nonneg_left hcore hV0
    _ ≤ L.V0 * (L.Htot ^ e * ((2 : ℝ) ^ κ)⁻¹ * ∏ p, L.ngen p) := by
        refine mul_le_mul_of_nonneg_left ?_ hV0
        refine mul_le_mul_of_nonneg_right ?_ hng
        exact mul_le_mul_of_nonneg_right hfin hk
    _ = ((2 : ℝ) ^ κ)⁻¹ * L.Htot ^ e * L.ngenTot := by
        unfold LocalNG.ngenTot
        ring

end

section

open Finset
open Classical

theorem t_MeanAmpJoint : Formalism.FourierDecayAlt.PN.MeanAmpJoint := by
  intro hS4 _ Cl Nu L C1 C0 r k hb hN hM hU S
  unfold e7
  have hH : ∀ p, 1 ≤ L.H p := hb.2.1
  have hnn : ∀ p, 0 ≤ L.nn p := hb.2.2.2.2.1
  refine mean hS4 L C0 r (k - 2 * r - 5) _ (fun p => L.H p ^ (C1 * (r + 1) ^ 2))
    (fun p => if p ∈ L.Om then 8 * L.H p ^ (C0 * (r + 1) ^ 2 + 2 * (2 * r + 2)) else 1)
    (fun p => one_le_pow₀ (hH p)) ?_ hb hM hU hN.1 hN.2 ?_ ?_ S
  · intro p
    show (1 : ℝ) ≤ if p ∈ L.Om then 8 * L.H p ^ (C0 * (r + 1) ^ 2 + 2 * (2 * r + 2)) else 1
    split_ifs
    · have : 1 ≤ L.H p ^ (C0 * (r + 1) ^ 2 + 2 * (2 * r + 2)) := one_le_pow₀ (hH p)
      linarith
    · exact le_refl _
  · intro p
    show L.nn p ≤ (if p ∈ L.Om then 8 * L.H p ^ (C0 * (r + 1) ^ 2 + 2 * (2 * r + 2)) else 1) * L.ngen p
    split_ifs with hp
    · exact hM.2 p hp
    · rw [one_mul, hM.1 p hp]
  · intro p
    show (if p ∈ L.Om then (4 : ℝ) else 1) * (L.H p ^ (C1 * (r + 1) ^ 2) *
      (if p ∈ L.Om then 8 * L.H p ^ (C0 * (r + 1) ^ 2 + 2 * (2 * r + 2)) else 1)) ≤
      L.H p ^ (C1 * (r + 1) ^ 2 + C0 * (r + 1) ^ 2 + 2 * (2 * r + 2) + 5)
    have e : L.H p ^ (C1 * (r + 1) ^ 2 + C0 * (r + 1) ^ 2 + 2 * (2 * r + 2) + 5) =
        L.H p ^ 5 * (L.H p ^ (C1 * (r + 1) ^ 2) * L.H p ^ (C0 * (r + 1) ^ 2 + 2 * (2 * r + 2))) := by
      rw [← pow_add, ← pow_add]; congr 1; ring
    have hA : 1 ≤ L.H p ^ (C1 * (r + 1) ^ 2) := one_le_pow₀ (hH p)
    have hB : 1 ≤ L.H p ^ (C0 * (r + 1) ^ 2 + 2 * (2 * r + 2)) := one_le_pow₀ (hH p)
    rw [e]
    split_ifs with hp
    · have h2 := two_le_H L hb p hp
      have h32 : (32 : ℝ) ≤ L.H p ^ 5 := by
        calc (32 : ℝ) = 2 ^ 5 := by norm_num
          _ ≤ L.H p ^ 5 := pow_le_pow_left₀ (by norm_num) h2 5
      have hpos : 0 ≤ L.H p ^ (C1 * (r + 1) ^ 2) * L.H p ^ (C0 * (r + 1) ^ 2 + 2 * (2 * r + 2)) := by
        positivity
      calc 4 * (L.H p ^ (C1 * (r + 1) ^ 2) * (8 * L.H p ^ (C0 * (r + 1) ^ 2 + 2 * (2 * r + 2))))
          = 32 * (L.H p ^ (C1 * (r + 1) ^ 2) * L.H p ^ (C0 * (r + 1) ^ 2 + 2 * (2 * r + 2))) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right h32 hpos
    · have h5 : 1 ≤ L.H p ^ 5 := one_le_pow₀ (hH p)
      rw [one_mul, mul_one]
      nlinarith [mul_le_mul h5 hB zero_le_one (le_trans zero_le_one h5)]

end

end Formalism.FourierDecayAlt.P.HermitianFormNormLemmas.B

namespace Formalism.FourierDecayAlt.P.HermitianFormNormLemmas.C

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.PN

section

open Finset

theorem fin_bound (hW : Formalism.HermitianLatticeCounting.S4.WeightedCS) {Cl J V : Type} [NormedAddCommGroup V] (U : Cl → J → V)
    (W : J → ℝ) (y : Cl → J → ℝ) (S1 M : ℝ) (hS1 : 0 ≤ S1)
    (hWpos : ∀ c j, U c j ≠ 0 → 0 < W j) (hy : ∀ c j, ‖U c j‖ ^ 2 ≤ y c j)
    (h1 : ∀ (c : Cl) (T : Finset J), (∀ j ∈ T, U c j ≠ 0) → ∑ j ∈ T, (W j)⁻¹ ≤ S1)
    (h2 : ∀ T : Finset (Cl × J), (∀ x ∈ T, U x.1 x.2 ≠ 0) → ∑ x ∈ T, W x.2 * y x.1 x.2 ≤ M)
    (Cs : Finset Cl) (T : Finset J) : ∑ c ∈ Cs, ‖∑ j ∈ T, U c j‖ ^ 2 ≤ S1 * M := by
  classical
  unfold Formalism.HermitianLatticeCounting.S4.WeightedCS at hW
  have hc : ∀ c ∈ Cs, ‖∑ j ∈ T, U c j‖ ^ 2 ≤ S1 * ∑ j ∈ T with U c j ≠ 0, W j * y c j := by
    intro c _
    have hW' : ‖∑ j ∈ T with U c j ≠ 0, U c j‖ ^ 2 ≤ (∑ j ∈ T with U c j ≠ 0, (W j)⁻¹) *
        ∑ j ∈ T with U c j ≠ 0, W j * ‖U c j‖ ^ 2 := by
      have h := hW (↥(T.filter (fun j => U c j ≠ 0))) V (fun j => U c j.1) (fun j => W j.1)
        (fun j => hWpos c j.1 (Finset.mem_filter.1 j.2).2)
      simp only [Finset.univ_eq_attach] at h
      rw [Finset.sum_attach _ (U c), Finset.sum_attach _ (fun j => (W j)⁻¹),
        Finset.sum_attach _ (fun j => W j * ‖U c j‖ ^ 2)] at h
      exact h
    have hs : ∑ j ∈ T with U c j ≠ 0, U c j = ∑ j ∈ T, U c j := Finset.sum_filter_ne_zero _
    rw [← hs]
    refine hW'.trans ?_
    refine mul_le_mul (h1 c _ (fun j hj => (Finset.mem_filter.1 hj).2))
      (Finset.sum_le_sum (fun j hj => mul_le_mul_of_nonneg_left (hy c j)
        (hWpos c j (Finset.mem_filter.1 hj).2).le)) ?_ hS1
    exact Finset.sum_nonneg (fun j hj => mul_nonneg (hWpos c j (Finset.mem_filter.1 hj).2).le
      (sq_nonneg _))
  calc ∑ c ∈ Cs, ‖∑ j ∈ T, U c j‖ ^ 2
      ≤ ∑ c ∈ Cs, S1 * ∑ j ∈ T with U c j ≠ 0, W j * y c j := Finset.sum_le_sum hc
    _ = S1 * ∑ x ∈ Cs ×ˢ T with U x.1 x.2 ≠ 0, W x.2 * y x.1 x.2 := by
        rw [← Finset.mul_sum]
        congr 1
        simp only [Finset.sum_filter, Finset.sum_product]
    _ ≤ S1 * M := mul_le_mul_of_nonneg_left (h2 _ (fun x hx => (Finset.mem_filter.1 hx).2)) hS1

theorem t_ClassCS : Formalism.FourierDecayAlt.PN.ClassCS := by
  unfold Formalism.FourierDecayAlt.PN.ClassCS
  intro hW Cl J V _ U W y Sw M h0 hWp hy h1 h2 Cs
  classical
  let U' : Cl → J → V := fun c j => if Summable (U c) then U c j else 0
  have hU'0 : ∀ c j, U' c j ≠ 0 → U c j ≠ 0 := by
    intro c j h hc
    apply h
    simp [U', hc]
  have hU'n : ∀ c j, ‖U' c j‖ ^ 2 ≤ y c j := by
    intro c j
    by_cases hs : Summable (U c)
    · have e : U' c j = U c j := by simp [U', hs]
      rw [e]
      exact hy c j
    · have e : U' c j = 0 := by simp [U', hs]
      rw [e, norm_zero]
      linarith [hy c j, sq_nonneg ‖U c j‖]
  have hsum : ∀ c, Summable (U' c) := by
    intro c
    by_cases hs : Summable (U c)
    · have e : U' c = U c := by funext j; simp [U', hs]
      rw [e]
      exact hs
    · have e : U' c = fun _ => 0 := by funext j; simp [U', hs]
      rw [e]
      exact summable_zero
  have htsum : ∀ c, ∑' j, U' c j = ∑' j, U c j := by
    intro c
    by_cases hs : Summable (U c)
    · have e : U' c = U c := by funext j; simp [U', hs]
      rw [e]
    · have e : U' c = fun _ => 0 := by funext j; simp [U', hs]
      rw [e, tsum_zero, tsum_eq_zero_of_not_summable hs]
  have hfin := fin_bound hW U' W y Sw M h0 (fun c j h => hWp c j (hU'0 c j h)) hU'n
    (fun c T hT => h1 c T (fun j hj => hU'0 c j (hT j hj)))
    (fun T hT => h2 T (fun x hx => hU'0 _ _ (hT x hx))) Cs
  have hlim : Filter.Tendsto (fun T : Finset J => ∑ c ∈ Cs, ‖∑ j ∈ T, U' c j‖ ^ 2) Filter.atTop
      (nhds (∑ c ∈ Cs, ‖∑' j, U' c j‖ ^ 2)) := by
    refine tendsto_finset_sum Cs (fun c _ => ?_)
    have ht : Filter.Tendsto (fun T : Finset J => ∑ j ∈ T, U' c j) Filter.atTop
        (nhds (∑' j, U' c j)) := (hsum c).hasSum
    exact ht.norm.pow 2
  have hle := le_of_tendsto' hlim hfin
  simpa only [htsum] using hle

end

section

open Finset

section
variable {ι V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

theorem summable_pairs (a : ι → V) (ha : Summable (fun i => ‖a i‖)) :
    Summable (fun p : ι × ι => (inner ℂ (a p.1) (a p.2) : ℂ)) := by
  have hprod : Summable (fun p : ι × ι => ‖a p.1‖ * ‖a p.2‖) :=
    Summable.mul_of_nonneg (f := fun i => ‖a i‖) (g := fun i => ‖a i‖) ha ha
      (fun i => norm_nonneg (a i)) (fun i => norm_nonneg (a i))
  have hb : Summable (fun p : ι × ι => ‖(inner ℂ (a p.1) (a p.2) : ℂ)‖) :=
    Summable.of_nonneg_of_le (fun p => norm_nonneg _)
      (fun p => norm_inner_le_norm (𝕜 := ℂ) (a p.1) (a p.2)) hprod
  exact hb.of_norm

theorem normsq_tsum (a : ι → V) (ha : Summable (fun i => ‖a i‖)) :
    ‖∑' i, a i‖ ^ 2 = ∑' p : ι × ι, (inner ℂ (a p.1) (a p.2) : ℂ).re := by
  have hS : HasSum a (∑' i, a i) := ha.of_norm.hasSum
  have hP : Summable (fun p : ι × ι => (inner ℂ (a p.1) (a p.2) : ℂ).re) :=
    Complex.reCLM.summable (summable_pairs a ha)
  have hfib : ∀ i, HasSum (fun j => (inner ℂ (a i) (a j) : ℂ).re)
      (inner ℂ (a i) (∑' j, a j) : ℂ).re := by
    intro i
    have h2 := Complex.reCLM.hasSum ((innerSL ℂ (a i)).hasSum hS)
    simpa using h2
  have hout : HasSum (fun i => (inner ℂ (a i) (∑' j, a j) : ℂ).re)
      (inner ℂ (∑' j, a j) (∑' j, a j) : ℂ).re := by
    have h2 : HasSum (fun i => (inner ℂ (∑' j, a j) (a i) : ℂ).re)
        (inner ℂ (∑' j, a j) (∑' j, a j) : ℂ).re := by
      simpa using Complex.reCLM.hasSum ((innerSL ℂ (∑' j, a j)).hasSum hS)
    have he : (fun i => (inner ℂ (a i) (∑' j, a j) : ℂ).re)
        = fun i => (inner ℂ (∑' j, a j) (a i) : ℂ).re := by
      funext i
      rw [← inner_conj_symm, Complex.conj_re]
    rw [he]
    exact h2
  have heq := hout.unique (hP.hasSum.prod_fiberwise hfib)
  rw [← heq]
  exact (inner_self_eq_norm_sq (𝕜 := ℂ) _).symm

end

theorem t_ClassSquaresSum : Formalism.FourierDecayAlt.PN.ClassSquaresSum := by
  intro ι C V _ _ _ v cl hv
  classical
  set A : C → ι → V := fun c => ({i | cl i = c} : Set ι).indicator v with hA
  have hAn : ∀ c, Summable (fun i => ‖A c i‖) := by
    intro c
    have : (fun i => ‖A c i‖) = ({i | cl i = c} : Set ι).indicator (fun i => ‖v i‖) := by
      funext i
      simp only [hA]
      exact norm_indicator_eq_indicator_norm _ _
    rw [this]
    exact hv.indicator _
  set G : C × (ι × ι) → ℝ := fun x => (inner ℂ (A x.1 x.2.1) (A x.1 x.2.2) : ℂ).re with hG
  set F : ι × ι → ℝ := ({p | cl p.1 = cl p.2} : Set (ι × ι)).indicator
        (fun p => (inner ℂ (v p.1) (v p.2) : ℂ).re) with hF
  set emb : ι × ι → C × (ι × ι) := fun p => (cl p.1, p) with hemb
  have hinj : Function.Injective emb := by
    intro p p' h
    exact (Prod.ext_iff.1 h).2
  have hGF : ∀ p, G (emb p) = F p := by
    intro p
    simp only [hG, hF, hemb, hA]
    by_cases h : cl p.1 = cl p.2
    · simp [Set.indicator, h]
    · have h' : ¬ cl p.2 = cl p.1 := fun e => h e.symm
      simp [Set.indicator, h, h']
  have hsupp : ∀ x, x ∉ Set.range emb → G x = 0 := by
    intro x hx
    have hc : ¬ cl x.2.1 = x.1 := by
      intro e
      exact hx ⟨x.2, by simp [hemb, e]⟩
    simp [hG, hA, Set.indicator, hc]
  have hFs : Summable F := by
    refine Summable.of_norm_bounded (g := fun p : ι × ι => ‖v p.1‖ * ‖v p.2‖)
      (Summable.mul_of_nonneg hv hv (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)) ?_
    intro p
    simp only [hF]
    by_cases h : cl p.1 = cl p.2
    · simp only [Set.indicator, Set.mem_ofPred_eq, h, if_true]
      exact (Complex.abs_re_le_norm _).trans (norm_inner_le_norm _ _)
    · simp only [Set.indicator, Set.mem_ofPred_eq, h, if_false, norm_zero]
      positivity
  have hGs : Summable G := by
    rw [← hinj.summable_iff hsupp]
    have : G ∘ emb = F := funext hGF
    rw [this]; exact hFs
  have hrow : ∀ c, ∑' p : ι × ι, G (c, p) = ‖∑' i, A c i‖ ^ 2 := by
    intro c
    exact (normsq_tsum (A c) (hAn c)).symm
  constructor
  · have := hGs.prod
    simpa only [hrow] using this
  · have e1 : ∑' p, F p = ∑' x, G x := by
      rw [← hinj.tsum_eq (f := G)]
      · exact tsum_congr (fun p => (hGF p).symm)
      · intro x hx
        by_contra hn
        exact hx (hsupp x hn)
    rw [e1, hGs.tsum_prod]
    exact tsum_congr hrow

end

end Formalism.FourierDecayAlt.P.HermitianFormNormLemmas.C

namespace Formalism.FourierDecayAlt.P.HermitianFormNormLemmas.D1

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.PN

section

open Finset
open Classical

theorem t_ExponentSumText : ExponentSumText := by
  intro r
  have h : (r + 1) ^ 2 = r ^ 2 + 2 * r + 1 := by ring
  rw [h]
  generalize r ^ 2 = s
  constructor <;> omega

theorem t_ExponentSum : ExponentSum := by
  intro C1 C0 A r hA
  unfold e7 eN
  have h1 : r + 1 ≤ (r + 1) ^ 2 := by nlinarith
  generalize (r + 1) ^ 2 = s at *
  have hA2 : (C1 + C0 + 38) * s ≤ A * s := Nat.mul_le_mul_right _ hA
  nlinarith

theorem t_FirstBracket : FirstBracket := by
  intro Γ Nu w Pn occ S1 hw hP hcard hsum T hT
  have hmaps : ∀ x ∈ T, x.1 ∈ T.image Prod.fst := fun x hx => mem_image_of_mem _ hx
  rw [← sum_fiberwise_of_maps_to hmaps]
  refine le_trans (sum_le_sum (g := fun γ => (w γ)⁻¹) ?_) (hsum _ ?_)
  · intro γ hγ
    obtain ⟨x0, hx0, rfl⟩ := mem_image.mp hγ
    have hPpos : 0 < Pn x0.1 := hP _ _ (hT x0 hx0)
    have hc : ∑ x ∈ T with x.1 = x0.1, (w x.1 * Pn x.1)⁻¹ =
        ((T.filter (fun x => x.1 = x0.1)).card : ℝ) * (w x0.1 * Pn x0.1)⁻¹ := by
      rw [sum_congr rfl (g := fun _ => (w x0.1 * Pn x0.1)⁻¹)]
      · rw [sum_const, nsmul_eq_mul]
      · intro x hx
        rw [(mem_filter.mp hx).2]
    rw [hc]
    have hinj : Set.InjOn Prod.snd ((T.filter (fun x => x.1 = x0.1) : Finset (Γ × Nu)) : Set (Γ × Nu)) := by
      intro a ha b hb hab
      have ha' := (mem_filter.mp (mem_coe.mp ha)).2
      have hb' := (mem_filter.mp (mem_coe.mp hb)).2
      exact Prod.ext (ha'.trans hb'.symm) hab
    have hcd : ((T.filter (fun x => x.1 = x0.1)).card : ℝ) ≤ Pn x0.1 := by
      rw [← card_image_of_injOn hinj]
      apply hcard
      intro ν hν
      obtain ⟨y, hy, rfl⟩ := mem_image.mp hν
      have hy' := mem_filter.mp hy
      rw [← hy'.2]
      exact hT y hy'.1
    have hwpos := hw x0.1
    calc ((T.filter (fun x => x.1 = x0.1)).card : ℝ) * (w x0.1 * Pn x0.1)⁻¹
        ≤ Pn x0.1 * (w x0.1 * Pn x0.1)⁻¹ := by
          apply mul_le_mul_of_nonneg_right hcd; positivity
      _ = (w x0.1)⁻¹ := by field_simp
  · intro γ hγ
    obtain ⟨x0, hx0, rfl⟩ := mem_image.mp hγ
    exact ⟨x0.2, hT x0 hx0⟩

end

end Formalism.FourierDecayAlt.P.HermitianFormNormLemmas.D1

namespace Formalism.FourierDecayAlt.P.HermitianFormNormLemmas.D2

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.PN

section

open Finset
open Classical

theorem t_SecondBracket : SecondBracket := by
  intro Cl Γ Nu isPt a2 w Jloc JB n NG ND Hh ngen κ2 cSt AAre e1 gf Pc TB e7 eN Aexp
    hκ hcSt hAA he1 hgf hPc hexp ha2 hpt hmean hmeas hmass hheight hTB T hT
  have hmaps : ∀ x ∈ T, x.2.1 ∈ T.image (fun x => x.2.1) := fun x hx => mem_image_of_mem _ hx
  rw [← sum_fiberwise_of_maps_to hmaps]
  set K : ℝ := κ2 * cSt * AAre * e1 * Pc * gf ^ Aexp with hK
  have hK0 : 0 ≤ K := by rw [hK]; positivity
  have hptI : ∀ γ ∈ T.image (fun x => x.2.1), isPt γ := by
    intro γ hγ
    obtain ⟨x0, hx0, rfl⟩ := mem_image.mp hγ
    exact hT x0 hx0
  have hfin : ∑ γ ∈ T.image (fun x => x.2.1), K * (w γ * n γ * (NG γ * ND γ) ^ Aexp * JB γ) ≤ K * TB := by
    rw [← mul_sum]
    exact mul_le_mul_of_nonneg_left (hTB _ hptI) hK0
  refine le_trans (sum_le_sum ?_) hfin
  intro γ hγ
  have hp := hptI γ hγ
  obtain ⟨hw, hJl, hJB, hn, hNG, hND, hH⟩ := hpt γ hp

  have hinner : ∑ x ∈ T with x.2.1 = γ, (w x.2.1 * (Pc * NG x.2.1 ^ 6)) * (a2 x.1 x.2.1 x.2.2 * Jloc x.2.1) =
      (w γ * (Pc * NG γ ^ 6) * Jloc γ) *
        ∑ y ∈ (T.filter (fun x => x.2.1 = γ)).image (fun x => (x.1, x.2.2)), a2 y.1 γ y.2 := by
    rw [sum_image]
    · rw [mul_sum]
      apply sum_congr rfl
      intro x hx
      rw [(mem_filter.mp hx).2]
      ring
    · intro a ha b hb hab
      have ha' := (mem_filter.mp (mem_coe.mp ha)).2
      have hb' := (mem_filter.mp (mem_coe.mp hb)).2
      have hab' : (a.1, a.2.2) = (b.1, b.2.2) := hab
      have h1 : a.1 = b.1 := (Prod.mk.inj hab').1
      have h2 : a.2.2 = b.2.2 := (Prod.mk.inj hab').2
      exact Prod.ext h1 (Prod.ext (ha'.trans hb'.symm) h2)
  rw [hinner]
  set σ : ℝ := ∑ y ∈ (T.filter (fun x => x.2.1 = γ)).image (fun x => (x.1, x.2.2)), a2 y.1 γ y.2 with hσ
  have hσ0 : 0 ≤ σ := sum_nonneg (fun y _ => ha2 _ _ _)
  have hH0 : 0 ≤ Hh γ := by linarith
  have hσ1 : σ ≤ κ2 * Hh γ ^ e7 * (AAre * e1 * Hh γ ^ eN * n γ) := by
    refine le_trans (hmean γ hp _) ?_
    exact mul_le_mul_of_nonneg_left (hmass γ hp) (by positivity)
  have hNG0 : 0 ≤ NG γ := by linarith
  have hND0 : 0 ≤ ND γ := by linarith
  have hF : w γ * (Pc * NG γ ^ 6) * Jloc γ ≤ w γ * (Pc * NG γ ^ 6) * (cSt * JB γ) :=
    mul_le_mul_of_nonneg_left (hmeas γ hp) (by positivity)
  have hstep : (w γ * (Pc * NG γ ^ 6) * Jloc γ) * σ ≤
      (w γ * (Pc * NG γ ^ 6) * (cSt * JB γ)) * (κ2 * Hh γ ^ e7 * (AAre * e1 * Hh γ ^ eN * n γ)) :=
    mul_le_mul hF hσ1 hσ0 (by positivity)
  refine le_trans hstep ?_

  set Xx : ℝ := NG γ * ND γ with hX
  have hX1 : 1 ≤ Xx := by rw [hX]; nlinarith
  have hX0 : 0 ≤ Xx := by linarith
  have hNGX : NG γ ≤ Xx := by rw [hX]; nlinarith
  have hHX : Hh γ ≤ gf * Xx := by rw [hX, ← mul_assoc]; exact hheight γ hp
  have hgf0 : 0 ≤ gf := by linarith
  have hpw : NG γ ^ 6 * (Hh γ ^ e7 * Hh γ ^ eN) ≤ gf ^ Aexp * Xx ^ Aexp := by
    rw [← pow_add]
    calc NG γ ^ 6 * Hh γ ^ (e7 + eN) ≤ Xx ^ 6 * (gf * Xx) ^ (e7 + eN) := by gcongr
      _ = gf ^ (e7 + eN) * Xx ^ (e7 + eN + 6) := by rw [mul_pow, pow_add Xx]; ring
      _ ≤ gf ^ Aexp * Xx ^ Aexp := by
          apply mul_le_mul (pow_le_pow_right₀ hgf (by omega)) (pow_le_pow_right₀ hX1 hexp)
            (by positivity) (by positivity)
  have hrest : 0 ≤ w γ * Pc * cSt * JB γ * κ2 * AAre * e1 * n γ := by positivity
  calc (w γ * (Pc * NG γ ^ 6) * (cSt * JB γ)) * (κ2 * Hh γ ^ e7 * (AAre * e1 * Hh γ ^ eN * n γ))
      = (w γ * Pc * cSt * JB γ * κ2 * AAre * e1 * n γ) * (NG γ ^ 6 * (Hh γ ^ e7 * Hh γ ^ eN)) := by ring
    _ ≤ (w γ * Pc * cSt * JB γ * κ2 * AAre * e1 * n γ) * (gf ^ Aexp * Xx ^ Aexp) :=
        mul_le_mul_of_nonneg_left hpw hrest
    _ = K * (w γ * n γ * Xx ^ Aexp * JB γ) := by rw [hK]; ring

end

end Formalism.FourierDecayAlt.P.HermitianFormNormLemmas.D2

namespace Formalism.FourierDecayAlt.P.HermitianFormNormLemmas.D3

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.PN

section

open Finset
open Classical

lemma hpow {b x c : ℝ} (hb : 1 < b) (hx0 : 0 ≤ x) (hx : x ≤ b ^ c) (n : ℕ) {K M : ℝ}
    (h : c * n ≤ K * M) : x ^ n ≤ Real.exp (K * M * Real.log b) := by
  have hb0 : 0 < b := by linarith
  have hlog : 0 < Real.log b := Real.log_pos hb
  calc x ^ n ≤ (b ^ c) ^ n := by gcongr
    _ = b ^ (c * (n : ℝ)) := by rw [← Real.rpow_natCast, ← Real.rpow_mul hb0.le]
    _ = Real.exp (Real.log b * (c * (n : ℝ))) := Real.rpow_def_of_pos hb0 _
    _ ≤ Real.exp (K * M * Real.log b) := by
      apply Real.exp_le_exp.mpr
      nlinarith

lemma hk {c t m5 f : ℝ} (hc : 0 ≤ c) (hf : 0 ≤ f) (ht : t ≤ m5) : c * (f * t) ≤ c * (m5 * f) := by
  rw [mul_comm m5 f]
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ht hf) hc

lemma core (A : ℕ) (CB CSt Cg CT : ℝ) (_hCB : 0 ≤ CB) (hCSt : 0 ≤ CSt) (hCg : 0 ≤ Cg) (hCT : 0 ≤ CT)
    (r f : ℕ) (b rd g TT cSt e1 m M : ℝ) (hm : m = 2 * (r : ℝ) + 2) (hM : M = m ^ 5 * f)
    (hf : 1 ≤ f) (hb : 16 ≤ b) (hrd0 : 0 < rd) (hrd : rd ≤ b) (hg1 : 1 ≤ g) (hg : g ≤ b ^ Cg)
    (hTT0 : 0 < TT) (hTT : TT ≤ b ^ (2 * CT * m)) (hc0 : 0 ≤ cSt) (hc : cSt ≤ b ^ (CSt * m ^ 3 * f))
    (he0 : 0 ≤ e1) (he : e1 ≤ 2) :
    (64 : ℝ) ^ (f * (r + 1)) * (cSt * e1 * (rd ^ (12 * r * (r + 1) * f) * TT ^ (6 * f)) *
          (g ^ f) ^ (A * (r + 1) ^ 2) * Real.exp (CB * M * Real.log b)) *
        ((rd / 2) ^ (f * (r + 1)) * g ^ (f * (r + 1) * (2 * r + 3))) ≤
      Real.exp ((2 + CSt + 1 + 12 + 12 * CT + Cg * A + CB + 1 + Cg) * M * Real.log b) := by
  have hb1 : (1 : ℝ) < b := by linarith
  have hR : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hF : (1 : ℝ) ≤ f := by exact_mod_cast hf
  have hF0 : (0 : ℝ) ≤ f := by linarith
  have hg0 : (0 : ℝ) ≤ g := by linarith
  have hm2 : (2 : ℝ) ≤ m := by rw [hm]; linarith
  have hm0 : (0 : ℝ) ≤ m := by linarith
  have hsq : (4 : ℝ) ≤ m ^ 2 := by
    have := mul_le_mul hm2 hm2 (by norm_num) hm0
    linarith
  have h3 : (8 : ℝ) ≤ m ^ 3 := by
    have := mul_le_mul hsq hm2 (by norm_num) (by positivity)
    linarith
  have h4 : (16 : ℝ) ≤ m ^ 4 := by
    have := mul_le_mul hsq hsq (by norm_num) (by positivity)
    linarith
  have h15 : m ≤ m ^ 5 := by
    have := mul_le_mul_of_nonneg_left (show (1 : ℝ) ≤ m ^ 4 by linarith) hm0
    linarith
  have h25 : m ^ 2 ≤ m ^ 5 := by
    have := mul_le_mul_of_nonneg_left (show (1 : ℝ) ≤ m ^ 3 by linarith) (pow_nonneg hm0 2)
    linarith
  have h35 : m ^ 3 ≤ m ^ 5 := by
    have := mul_le_mul_of_nonneg_left (show (1 : ℝ) ≤ m ^ 2 by linarith) (pow_nonneg hm0 3)
    linarith
  have hM1 : (1 : ℝ) ≤ M := by
    rw [hM]
    have := mul_le_mul_of_nonneg_left hF (pow_nonneg hm0 5)
    linarith
  have hRm : (r : ℝ) + 1 ≤ m := by rw [hm]; linarith
  have hRR : (r : ℝ) * (r + 1) ≤ m ^ 2 := by rw [hm]; linarith [sq_nonneg (r : ℝ)]
  have hR2 : ((r : ℝ) + 1) ^ 2 ≤ m ^ 2 := by rw [hm]; linarith [sq_nonneg (r : ℝ)]
  have hR3 : ((r : ℝ) + 1) * (2 * r + 3) ≤ m ^ 2 := by rw [hm]; linarith [sq_nonneg (r : ℝ)]
  have h64 : (64 : ℝ) ^ (f * (r + 1)) ≤ Real.exp (2 * M * Real.log b) :=
    hpow hb1 (by norm_num) (by
      rw [Real.rpow_two]
      have := mul_le_mul hb hb (by norm_num) (by linarith)
      linarith) _
      (by push_cast; rw [hM]; linarith [mul_le_mul_of_nonneg_right (hRm.trans h15) hF0])
  have hcS : cSt ≤ Real.exp (CSt * M * Real.log b) := by
    have h := hpow hb1 hc0 hc 1 (K := CSt) (M := M)
      (by push_cast; rw [hM]; linarith [mul_nonneg (mul_nonneg hCSt (sub_nonneg.2 h35)) hF0])
    rwa [pow_one] at h
  have he1 : e1 ≤ Real.exp (1 * M * Real.log b) := by
    have h := hpow hb1 he0 (show e1 ≤ b ^ (1 : ℝ) by rw [Real.rpow_one]; linarith) 1 (K := 1) (M := M)
      (by push_cast; linarith)
    rwa [pow_one] at h
  have hrdb : rd ^ (12 * r * (r + 1) * f) ≤ Real.exp (12 * M * Real.log b) :=
    hpow hb1 hrd0.le (show rd ≤ b ^ (1 : ℝ) by rw [Real.rpow_one]; exact hrd) _
      (by push_cast; rw [hM]; linarith [mul_le_mul_of_nonneg_right (hRR.trans h25) hF0])
  have hTTb : TT ^ (6 * f) ≤ Real.exp (12 * CT * M * Real.log b) :=
    hpow hb1 hTT0.le hTT _
      (by push_cast; rw [hM]; linarith [mul_nonneg (mul_nonneg hCT (sub_nonneg.2 h15)) hF0])
  have hgA : (g ^ f) ^ (A * (r + 1) ^ 2) ≤ Real.exp (Cg * A * M * Real.log b) := by
    rw [← pow_mul]
    exact hpow hb1 hg0 hg _ (by
      push_cast; rw [hM]
      linarith [mul_nonneg (mul_nonneg (mul_nonneg hCg (Nat.cast_nonneg A))
        (sub_nonneg.2 (hR2.trans h25))) hF0])
  have hrd2 : (rd / 2) ^ (f * (r + 1)) ≤ Real.exp (1 * M * Real.log b) :=
    hpow hb1 (div_nonneg hrd0.le (by norm_num)) (show rd / 2 ≤ b ^ (1 : ℝ) by rw [Real.rpow_one]; linarith) _
      (by push_cast; rw [hM]; linarith [mul_le_mul_of_nonneg_right (hRm.trans h15) hF0])
  have hgg : g ^ (f * (r + 1) * (2 * r + 3)) ≤ Real.exp (Cg * M * Real.log b) :=
    hpow hb1 hg0 hg _
      (by push_cast; rw [hM]; linarith [mul_nonneg (mul_nonneg hCg (sub_nonneg.2 (hR3.trans h25))) hF0])
  have hp1 := mul_le_mul hcS he1 he0 (Real.exp_pos _).le
  have hp2 := mul_le_mul hrdb hTTb (pow_nonneg hTT0.le _) (Real.exp_pos _).le
  have hp3 := mul_le_mul hp1 hp2 (mul_nonneg (pow_nonneg hrd0.le _) (pow_nonneg hTT0.le _)) (by positivity)
  have hp4 := mul_le_mul hp3 hgA (pow_nonneg (pow_nonneg hg0 _) _) (by positivity)
  have hp5 := mul_le_mul_of_nonneg_right hp4 (Real.exp_pos (CB * M * Real.log b)).le
  have hp6 := mul_le_mul h64 hp5
    (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hc0 he0)
      (mul_nonneg (pow_nonneg hrd0.le _) (pow_nonneg hTT0.le _))) (pow_nonneg (pow_nonneg hg0 _) _))
      (Real.exp_pos _).le) (Real.exp_pos _).le
  have hp7 := mul_le_mul hrd2 hgg (pow_nonneg hg0 _) (Real.exp_pos _).le
  have hp8 := mul_le_mul hp6 hp7
    (mul_nonneg (pow_nonneg (div_nonneg hrd0.le (by norm_num)) _) (pow_nonneg hg0 _)) (by positivity)
  refine hp8.trans (le_of_eq ?_)
  simp only [← Real.exp_add]
  congr 1
  ring

theorem t_NGNumbers : NGNumbers := by
  unfold NGNumbers
  intro A CB CSt Cg CT hCB hCSt hCg hCT
  refine ⟨2 + CSt + 1 + 12 + 12 * CT + Cg * A + CB + 1 + Cg, ?_, ?_⟩
  · have := mul_nonneg hCg (Nat.cast_nonneg A : (0 : ℝ) ≤ A)
    linarith
  intro r f b rd g TT cSt e1 hS
  unfold NGSizes at hS
  obtain ⟨hf, hb, hrd0, hrd, hg1, hg, hTT0, hTT, hc0, hc, he0, he⟩ := hS
  have h := core A CB CSt Cg CT hCB hCSt hCg hCT r f b rd g TT cSt e1 (((2 * r + 2 : ℕ) : ℝ))
    (((2 * r + 2 : ℕ) : ℝ) ^ 5 * f) (by push_cast <;> ring) rfl hf hb hrd0 hrd hg1 hg hTT0 hTT hc0 hc
    he0 he
  have e : ∀ K : ℝ, K * (((2 * r + 2 : ℕ) : ℝ) ^ 5 * f) * Real.log b =
      K * ((2 * r + 2 : ℕ) : ℝ) ^ 5 * f * Real.log b := fun K => by ring
  rw [e, e] at h
  exact h

end

end Formalism.FourierDecayAlt.P.HermitianFormNormLemmas.D3

namespace Formalism.FourierDecayAlt.P.HermitianFormNormLemmas.E

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.PN

section

open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.PN
open scoped ComplexOrder ComplexConjugate
open Classical

theorem t_RowFromClasses : Formalism.FourierDecayAlt.PN.RowFromClasses := by
  intro hCS τ Rw I H H₁ _ _ _ _ _ _ X E _ r Cl Nu N hAbs hCl
  obtain ⟨_, hvec, hG⟩ := hAbs
  set v : τ → H₁ := X.ngSet.indicator X.vec with hv
  have hvs : Summable (fun i => ‖v i‖) := by
    have : (fun i => ‖v i‖) = X.ngSet.indicator (fun i => ‖X.vec i‖) := by
      funext i; simp [hv, norm_indicator_eq_indicator_norm]
    rw [this]; exact hvec.indicator _
  obtain ⟨hsum, heq⟩ := hCS τ Cl H₁ v N.cls hvs
  have key : ∀ c, ∑' i, ({i | N.cls i = c} : Set τ).indicator v i =
      ∑' x : Pts E r × Nu, grp X N c x.1 x.2 := by
    intro c
    set u : τ → H₁ := ({i | N.cls i = c} : Set τ).indicator v with hu
    have hus : Summable u := by
      have h1 : Summable v := hvs.of_norm
      exact h1.indicator _
    have h2 := (hus.hasSum.tsum_fiberwise (fun t => (N.pt t, N.nml t))).tsum_eq
    rw [← h2]
    apply tsum_congr
    intro x
    rw [_root_.tsum_subtype]
    unfold grp
    apply tsum_congr
    intro t
    by_cases h1 : t ∈ X.ngSet <;> by_cases h2 : N.cls t = c <;> by_cases h3 : N.pt t = x.1 <;>
      by_cases h4 : N.nml t = x.2 <;>
      simp [hu, hv, Set.indicator, h1, h2, h3, h4, Prod.ext_iff]
  have hfun : (fun c => ‖∑' i, ({i | N.cls i = c} : Set τ).indicator v i‖ ^ 2) =
      (fun c => ‖∑' x : Pts E r × Nu, grp X N c x.1 x.2‖ ^ 2) := by
    funext c; rw [key c]
  refine ⟨hfun ▸ hsum, ?_⟩
  rw [← hfun, ← heq]
  unfold PB.Terms.pairSum
  congr 1
  apply tsum_congr
  intro p
  by_cases h1 : p.1 ∈ X.ngSet
  · by_cases h2 : p.2 ∈ X.ngSet
    · have hiff := hCl p.1 h1 p.2 h2
      by_cases h3 : N.cls p.1 = N.cls p.2
      · have h4 := hiff.2 h3
        have hm : p ∈ X.one X.ngSet := ⟨⟨h1, h2, h4.1⟩, h4.2⟩
        simp [Set.indicator, hm, h3, hv, h1, h2]
      · have hm : p ∉ X.one X.ngSet := fun hm => h3 (hiff.1 ⟨hm.1.2.2, hm.2⟩)
        simp [Set.indicator, hm, h3]
    · have hm : p ∉ X.one X.ngSet := fun hm => h2 hm.1.2.1
      simp [Set.indicator, hm, hv, h2]
  · have hm : p ∉ X.one X.ngSet := fun hm => h1 hm.1.1
    simp [Set.indicator, hm, hv, h1]

theorem blockMinorWeight_pos {E : Type} [Field E] [NumberField E] {r : ℕ} (γ : Pts E r) :
    0 < Formalism.HermitianLatticeCounting.ExpansionTerms.blockMinorWeight γ := by
  unfold Formalism.HermitianLatticeCounting.ExpansionTerms.blockMinorWeight
  exact Finset.prod_pos fun a _ => Finset.prod_pos fun w _ => by positivity

theorem occ_of_ne {τ Rw I H H₁ : Type} [Fintype I] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] (X : PB.Terms τ Rw I H H₁)
    {E : Type} [Field E] {r : ℕ} {Cl Nu : Type} (N : NGData τ E r Cl Nu) (c : Cl) (γ : Pts E r) (ν : Nu)
    (h : grp X N c γ ν ≠ 0) : Occ X N c γ ν := by
  by_contra hno
  apply h
  have hz : ∀ t, (X.ngSet ∩ {t | N.cls t = c ∧ N.pt t = γ ∧ N.nml t = ν}).indicator X.vec t = 0 := by
    intro t
    by_cases ht : t ∈ X.ngSet ∩ {t | N.cls t = c ∧ N.pt t = γ ∧ N.nml t = ν}
    · rw [Set.indicator_of_mem ht]
      by_contra hv
      exact hno ⟨t, ht.1, hv, ht.2.1, ht.2.2.1, ht.2.2.2⟩
    · simp [Set.indicator_apply, ht]
  unfold Formalism.FourierDecayAlt.PN.grp
  simp only [hz, tsum_zero]

theorem t_GenMassOfSplit : Formalism.FourierDecayAlt.PN.GenMassOfSplit := by
  intro τ Rw I H H₁ _ _ _ _ _ X E _ r Cl Nu N AAre e1 Gk dens tw hA hH h γ hγ
  obtain ⟨hG, ht, hn, hd0, hd, htw, hm⟩ := h γ hγ
  have hH1 := hH γ hγ
  have hH0 : 0 ≤ N.Hh γ := by linarith
  refine ⟨by rw [hn]; positivity, hm.trans ?_⟩
  have hGk : Gk γ ≤ N.n γ * N.Hh γ ^ (6 * (2 * r + 2)) := by
    have : Gk γ = N.n γ * (tw γ)⁻¹ := by rw [hn]; field_simp
    rw [this]
    exact mul_le_mul_of_nonneg_left htw (by rw [hn]; positivity)
  have hn0 : 0 ≤ N.n γ := by rw [hn]; positivity
  have he1 : 0 ≤ e1 * N.Hh γ := hd0.trans hd
  calc AAre * Gk γ * dens γ * N.Hh γ ^ (10 * (r + 1) ^ 2)
      ≤ AAre * (N.n γ * N.Hh γ ^ (6 * (2 * r + 2))) * (e1 * N.Hh γ) * N.Hh γ ^ (10 * (r + 1) ^ 2) := by
        gcongr
    _ = AAre * e1 * N.Hh γ ^ eN r * N.n γ := by
        unfold eN; ring

theorem t_RowNGAbstract : Formalism.FourierDecayAlt.PN.RowNGAbstract := by
  intro hC hCSS hRFC hCCS hFB hSB hMA E _ _ _ τ Rw I H H₁ _ _ _ _ _ _ X r k Cl Nu N C1 C0 Aexp
    Pc gf cSt AAre e1 TB hexp hPc hgf hcSt hAA he1 hAbs hClass hAmp hNorm hPts hLoc hMeas hGen hHt hTB
  obtain ⟨hStep4, hOm, hWCS, hE5⟩ := hC
  obtain ⟨hsum, heq⟩ := hRFC hCSS τ Rw I H H₁ X E r Cl Nu N hAbs hClass
  rw [heq]
  have hG : 0 < X.Gam1 := hAbs.2.2
  apply mul_le_mul_of_nonneg_left _ hG.le
  apply hsum.tsum_le_of_sum_le
  intro Cs
  have hW : ∀ γ, IsPt X N γ → 0 < Formalism.HermitianLatticeCounting.ExpansionTerms.blockMinorWeight γ * (Pc * N.NG γ ^ 6) := by
    intro γ hγ
    have h1 := (hHt γ hγ).1
    have := blockMinorWeight_pos γ
    positivity
  refine hCCS hWCS Cl (Pts E r × Nu) H₁ (fun c x => grp X N c x.1 x.2)
    (fun x => Formalism.HermitianLatticeCounting.ExpansionTerms.blockMinorWeight x.1 * (Pc * N.NG x.1 ^ 6))
    (fun c x => N.a2 c x.1 x.2 * N.J2loc x.1) _ _ (by positivity) ?_ ?_ ?_ ?_ Cs
  · intro c j hj
    exact hW j.1 ⟨c, j.2, occ_of_ne X N c j.1 j.2 hj⟩
  · intro c j
    exact hAmp.2.2 c j.1 j.2
  · intro c T hT
    refine hFB (Pts E r) Nu Formalism.HermitianLatticeCounting.ExpansionTerms.blockMinorWeight (fun γ => Pc * N.NG γ ^ 6) (Occ X N c) _
      (fun γ => blockMinorWeight_pos γ) ?_ ?_ ?_ T (fun x hx => occ_of_ne X N c x.1 x.2 (hT x hx))
    · intro γ ν hο
      have h1 := (hHt γ ⟨c, ν, hο⟩).1
      positivity
    · intro γ S hS
      exact hNorm c γ S hS
    · intro S hS
      refine hE5 E r S (fun γ hγ => ?_)
      obtain ⟨ν, hν⟩ := hS γ hγ
      exact hPts γ ⟨c, ν, hν⟩
  · intro T hT
    refine hSB Cl (Pts E r) Nu (IsPt X N) N.a2 Formalism.HermitianLatticeCounting.ExpansionTerms.blockMinorWeight N.J2loc N.jacobianSquareBound N.n N.NG N.ND N.Hh N.ngen
      (((2 : ℝ) ^ (k - 2 * r - 5))⁻¹) cSt AAre e1 gf Pc TB (e7 C1 C0 r) (eN r) Aexp
      (by positivity) hcSt hAA he1 hgf hPc.le hexp hAmp.1 ?_ ?_ ?_ ?_ ?_ hTB T ?_
    · intro γ hγ
      obtain ⟨L, hB, _, _, _, _, hH, _⟩ := hLoc γ hγ ∅
      refine ⟨blockMinorWeight_pos γ, hAmp.2.1 γ, (hMeas γ hγ).1, (hGen γ hγ).1, (hHt γ hγ).1, (hHt γ hγ).2.1, ?_⟩
      rw [hH]
      unfold LocalNG.Htot
      exact Finset.prod_induction _ (fun x => 1 ≤ x)
        (fun a b ha hb => one_le_mul_of_one_le_of_one_le ha hb) le_rfl (fun p _ => hB.2.1 p)
    · intro γ hγ S
      obtain ⟨L, hB, hNG, hMR, hU, ha, hH, hn⟩ := hLoc γ hγ S
      have := hMA hStep4 hOm Cl Nu L C1 C0 r k hB hNG hMR hU S
      rw [Finset.sum_congr rfl ha, hH, hn]
      exact this
    · intro γ hγ; exact (hMeas γ hγ).2
    · intro γ hγ; exact (hGen γ hγ).2
    · intro γ hγ; exact (hHt γ hγ).2.2
    · intro x hx
      exact ⟨x.1, x.2.2, occ_of_ne X N x.1 x.2.1 x.2.2 (hT x hx)⟩

end

end Formalism.FourierDecayAlt.P.HermitianFormNormLemmas.E

namespace Formalism.FourierDecayAlt.P.HermitianFormNormLemmas.F

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.PN

section

open Finset NumberField
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.PN

lemma pos_facts {P : Type} [Fintype P] (B : S3.MassData P) (h : B.Pos) :
    0 < B.AA ∧ 0 < B.d * B.d' / B.Dstar := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hAA, hD⟩ := Formalism.FourierDecayAlt.P.HermitianFormNormLemmas.A.book_constants_pos_of_pos B h
  have hd : 0 < B.d := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hd' : 0 < B.d' := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  exact ⟨hAA, div_pos (mul_pos hd hd') hD⟩

theorem t_RowNGJoint : RowNGJoint := by
  intro hch C1 C0 A CB CSt Cg CT hCB hCSt hCg hCT hA
  obtain ⟨hc48, hCSS, hRFC, hCCS, hFB, hSB, hMA, hRA, hNorm, hFP, hNR, hES, hNum⟩ := hch
  obtain ⟨Cn, hCn0, hCn⟩ := hNum A CB CSt Cg CT hCB hCSt hCg hCT
  refine ⟨Cn, hCn0, ?_⟩
  intro E _ _ _ τ Rw I H H₁ _ _ _ _ _ _ X r k Cl Nu N P _ B b rd g TT cSt e1 Irat Ire hAbs hGam hNI hFI
    hSz hIn
  obtain ⟨hCl, hAmp, hNo, hPt, hLoc, hMe, hGM, hHt, hTB⟩ := hIn
  have hnum := hCn r _ b rd g TT cSt e1 hSz
  obtain ⟨hf, hb, hrd, hrdb, hg1, hgb, hTT, hTTb, hcSt, hcStb, he1, he12⟩ := hSz
  obtain ⟨hAApos, hddpos⟩ := pos_facts B hNI.1
  have hLam : 0 < abelian₂ rd r k (Fintype.card (InfinitePlace E)) := by
    unfold abelian₂; positivity
  have hrow := hRA hc48 hCSS hRFC hCCS hFB hSB hMA E τ Rw I H H₁ X r k Cl Nu N C1 C0 (A * (r + 1) ^ 2)
    _ _ cSt _ e1 _ (hES C1 C0 A r hA) (by positivity) (one_le_pow₀ hg1) hcSt
    (le_of_lt (mul_pos hLam hAApos)) he1 hAbs hCl hAmp hNo hPt hLoc hMe hGM hHt hTB
  have hnr := hNR hNorm hFP P B rd g r k _ Irat Ire hNI hFI
  unfold PB.Terms.RowNG
  refine le_trans hrow ?_
  rw [hGam]
  generalize Fintype.card (InfinitePlace E) = f at *
  set κ : ℝ := ((2 : ℝ) ^ (k - 2 * r - 5))⁻¹ with hκ
  have hκ0 : 0 ≤ κ := by rw [hκ]; positivity
  set S : ℝ := 64 ^ (f * (r + 1)) with hS
  set Pc : ℝ := rd ^ (12 * r * (r + 1) * f) * TT ^ (6 * f) with hPc
  set gA : ℝ := (g ^ f) ^ (A * (r + 1) ^ 2) with hgA
  set ex : ℝ := Real.exp (CB * ((2 * r + 2 : ℕ) : ℝ) ^ 5 * f * Real.log b) with hex
  set vg : ℝ := (rd / 2) ^ (f * (r + 1)) * g ^ (f * (r + 1) * (2 * r + 3)) with hvg
  set dd : ℝ := B.d * B.d' / B.Dstar with hdd
  set AAre : ℝ := abelian₂ rd r k f * B.AA with hAAre
  set EX : ℝ := Real.exp (Cn * ((2 * r + 2 : ℕ) : ℝ) ^ 5 * f * Real.log b) with hEX
  have hS0 : 0 ≤ S := by rw [hS]; positivity
  have hPc0 : 0 ≤ Pc := by rw [hPc]; positivity
  have hgA0 : 0 ≤ gA := by rw [hgA]; positivity
  have hex0 : 0 ≤ ex := by rw [hex]; positivity
  have hF : 0 ≤ S * κ * cSt * e1 * Pc * gA * ex := by positivity
  calc B.Gam1 * (S * (κ * cSt * AAre * e1 * Pc * gA * (ex * Ire)))
      = (S * κ * cSt * e1 * Pc * gA * ex) * (B.Gam1 * AAre * Ire) := by ring
    _ ≤ (S * κ * cSt * e1 * Pc * gA * ex) * (vg * dd) := mul_le_mul_of_nonneg_left hnr hF
    _ = κ * (S * (cSt * e1 * Pc * gA * ex) * vg) * dd := by ring
    _ ≤ κ * EX * dd := by
        apply mul_le_mul_of_nonneg_right _ hddpos.le
        exact mul_le_mul_of_nonneg_left hnum hκ0

theorem t_PairBoundFromLocalNG : PairBoundFromLocalNG := by
  intro hPBL hPBC hRow hCh hLoop C₄ Cthr CL hC4 hCL C1 C0n A CB CSt Cg CT hCB hCSt hCg hCT hA
  obtain ⟨hMR, hPB, hLC, hGC, hLL, hAx, hA13, hPBA, hPI, hEI, hPS, hSF, hNP, hNE, hND, hNL, hNNG, hNGE,
    hEZ⟩ := hPBC
  obtain ⟨hNDS, hDS, hS0, hGS, hB3, hLJ, hLGR⟩ := hLoop
  obtain ⟨CA, C, h1, h2, h3, h4, hrest⟩ := hPBL hMR hPB hLC hGC hLL hAx hA13 hPBA hPI hEI hPS hSF hNP hNE
    hND hNL hNNG hNGE hEZ C₄ Cthr hC4
  obtain ⟨K₀, hK⟩ := hLJ hNDS hDS hS0 hGS hB3 CL hCL
  obtain ⟨Cn, hCn0, hCn⟩ := hRow hCh C1 C0n A CB CSt Cg CT hCB hCSt hCg hCT hA
  refine ⟨CA, C, K₀, Cn, h1, h2, h3, h4, hCn0, ?_⟩
  intro C0 CG CDel cT Cb a1 a2 a3 a4 a5 a6
  obtain ⟨k0, hk0⟩ := hrest C0 CG CDel cT Cb a1 a2 a3 a4 a5 a6
  refine ⟨k0, ?_⟩
  intro E W _ _ _ D e G bb Cp Cf Th de de' T T' du du' l hk hSz hc1 hc2 hUn hInst hLM jn H _ _ _ Vt c sd
    hRI hDI P _ B hRows hMassData hEL τ Rw I HS H₁ _ _ _ _ _ _ X hLink hSplit hSN Al NT Gam Xi hAl hPar hXi
    hlog hLI Cl Nu N cSt e1 Irat Ire hFI hNS hNI
  have hAbs : X.AbsConv := hSplit.1
  have hLink' := hLink
  obtain ⟨hG1, hSig, htyp, hd, hd', hDs⟩ := hLink'
  obtain ⟨bPos, bForm, bMass, bJac, bNu, bInf, bVol, bLev, bMas, bCol, bOrd, bTyp, bInd⟩ := hMassData
  have hNormI : NormInputs B := ⟨bPos, bJac, bNu, bInf, bVol, bLev, bMas, bCol, bOrd, bTyp, bInd⟩
  have hddpos := (pos_facts B bPos).2
  rw [hd, hd', hDs] at hddpos
  have hloops := hK τ Rw I HS H₁ X G.k G.r G.f Al bb G.g G.v NT Gam Xi _ hAl hPar hXi hlog hddpos.le hLI
  obtain ⟨hBig, hNSc⟩ := hLGR hSF τ Rw I HS H₁ X _ _ hAbs hloops
  have hng := hCn E τ Rw I HS H₁ X G.r G.k Cl Nu N P B bb (2 * G.v) G.g ((T : ℝ) * T') cSt e1 Irat Ire hAbs
    hG1 hNormI hFI hNS hNI
  rw [hd, hd', hDs] at hng
  exact hk0 E W D e G bb Cp Cf Th de de' T T' du du' l hk hSz hc1 hc2 hUn hInst hLM jn H Vt c sd hRI hDI P B
    hRows ⟨bPos, bForm, bMass, bJac, bNu, bInf, bVol, bLev, bMas, bCol, bOrd, bTyp, bInd⟩ hEL τ Rw I HS H₁ X
    (1 / 3) Cn hLink hSplit hSN hBig hNSc hng

end

end Formalism.FourierDecayAlt.P.HermitianFormNormLemmas.F

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt

theorem norm_of_leading_term : Formalism.FourierDecayAlt.PN.NormOfMain := HermitianFormNormLemmas.A.t_NormOfMain

theorem norm_of_lemmas : Formalism.FourierDecayAlt.PN.NormOfLemmas := HermitianFormNormLemmas.A.t_NormOfLemmas

theorem pn_norm_bound : Formalism.FourierDecayAlt.PN.NormBound :=
  norm_of_lemmas jacobian_natural_measure_constant local_ratio_product column_identity

theorem frame_passage : Formalism.FourierDecayAlt.PN.FramePassage := HermitianFormNormLemmas.A.t_FramePassage

theorem norm_real_part : Formalism.FourierDecayAlt.PN.NormRe := HermitianFormNormLemmas.A.t_NormRe

theorem pn_zpow_form : Formalism.FourierDecayAlt.PN.ZpowForm := HermitianFormNormLemmas.B.t_ZpowForm

theorem mean_amplitude_joint : Formalism.FourierDecayAlt.PN.MeanAmpJoint := HermitianFormNormLemmas.B.t_MeanAmpJoint

theorem class_squares_sum : Formalism.FourierDecayAlt.PN.ClassSquaresSum := HermitianFormNormLemmas.C.t_ClassSquaresSum

theorem class_cauchy_schwarz : Formalism.FourierDecayAlt.PN.ClassCS := HermitianFormNormLemmas.C.t_ClassCS

theorem first_bracket : Formalism.FourierDecayAlt.PN.FirstBracket := HermitianFormNormLemmas.D1.t_FirstBracket

theorem second_bracket : Formalism.FourierDecayAlt.PN.SecondBracket := HermitianFormNormLemmas.D2.t_SecondBracket

theorem line_from_classes : Formalism.FourierDecayAlt.PN.RowFromClasses := HermitianFormNormLemmas.E.t_RowFromClasses

theorem general_mass_of_split : Formalism.FourierDecayAlt.PN.GenMassOfSplit := HermitianFormNormLemmas.E.t_GenMassOfSplit

theorem line_norm_abstract : Formalism.FourierDecayAlt.PN.RowNGAbstract := HermitianFormNormLemmas.E.t_RowNGAbstract

theorem exponent_sum : Formalism.FourierDecayAlt.PN.ExponentSum := HermitianFormNormLemmas.D1.t_ExponentSum

theorem exponent_sum_explicit : Formalism.FourierDecayAlt.PN.ExponentSumText := HermitianFormNormLemmas.D1.t_ExponentSumText

theorem norm_numbers : Formalism.FourierDecayAlt.PN.NGNumbers := HermitianFormNormLemmas.D3.t_NGNumbers

theorem line_norm_joint : Formalism.FourierDecayAlt.PN.RowNGJoint := HermitianFormNormLemmas.F.t_RowNGJoint

theorem pair_bound_from_local_norm : Formalism.FourierDecayAlt.PN.PairBoundFromLocalNG := HermitianFormNormLemmas.F.t_PairBoundFromLocalNG

end Formalism.FourierDecayAlt.P
