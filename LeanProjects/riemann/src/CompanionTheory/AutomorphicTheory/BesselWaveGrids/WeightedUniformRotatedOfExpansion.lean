import CompanionTheory.AutomorphicTheory.BesselWaveGrids.TiedNum
import CompanionTheory.AutomorphicTheory.BesselWaveGrids.NormalizedMeasureScaling
import CompanionTheory.AutomorphicTheory.BesselWaveGrids.PowFourLeRpowNineHalves
import Formalism.SharpRestriction.CuspSpanNormBounds.TheoremBConstants
import Formalism.SharpRestriction.CuspSpanNormBounds.RatioInvLeFrameFactor

noncomputable section

namespace CompanionTheory.WaveGrid.WGlue

open MeasureTheory Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.MainNotions.OnePlaceEstimates Formalism.MainNotions.BesselShellMomentBounds Formalism.MainNotions.TheoremBConstants
  Formalism.MainNotions.BigCellDensity Formalism.L2.SG.Pf.BesselExpansion
open CompanionTheory.WaveGrid CompanionTheory.WaveGrid.Tied
open scoped ENNReal

def WIneq {k r : ℕ} (L : LocBessel k r) (f : Mx k r → (L.Wq →L[ℂ] L.Wp))
    (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (γ : Point ℂ (r + 1)) (w K : ℝ) : Prop :=
  ENNReal.ofReal (w * ptWeight k r (Tz k r L.z) (Tz k r L.z') γ) * orbSq L f γ ≤ ENNReal.ofReal K * jNorm2 L f μsec

def WLoc1 (D : D7) (Ch Cg Ca C : ℝ) (N : LocBessel D.R.k D.R.rS → Prop) : Prop :=
  ∀ (L : LocBessel D.R.k D.R.rS) (f : Mx D.R.k D.R.rS → (L.Wq →L[ℂ] L.Wp))
    (μsec : ℂ → Matrix (Fin (D.R.k + 1)) (Fin (D.R.k + 1)) ℂ) (ka b : ℝ), N L → LocOk D Ch Cg L L.lam ka b 1 →
    AllGaps L.lam (Cg * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 4) → IsKFinCoefH L.σ f → IsSection D.R.k D.R.rS L.z L.z' μsec →
    ∀ (l : Fin (D.R.rS + 1)) (a : ℕ), (a : ℝ) ≤ Ca * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 3 → ∀ γ : Point ℂ (D.R.rS + 1),
      Gpt (Tz D.R.k D.R.rS L.z) (Tz D.R.k D.R.rS L.z') γ ≠ 0 →
      WIneq L f μsec γ (‖Dpt γ l‖ ^ (2 * a)) (b ^ (C * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 5) *
        max 1 (1 / Gpt (Tz D.R.k D.R.rS L.z) (Tz D.R.k D.R.rS L.z') γ) ^ (40 * (D.R.rS + 1) ^ 2))

set_option maxHeartbeats 1600000 in
theorem wLoc1N_of (hW : ∀ Cb, WEnd.WBp Cb) {Cgc : ℝ} (hCC : CoefCC1 Cgc) (Ch Ca : ℝ) :
    ∃ C Cg₀ : ℝ, 0 ≤ C ∧ ∀ Cg, Cg₀ ≤ Cg → ∀ D : D7,
      WLoc1 D Ch Cg Ca C fun L => L.μN = Formalism.FourierDecayAlt.D.muN D.R.k D.R.rS := by
  obtain ⟨Cb, hPl⟩ := TypeHC.exists_place
  obtain ⟨C₅, Cg₁, hC5, H⟩ := hW Cb (2 * |Ch|) Ca (by positivity)
  refine ⟨C₅ + 8, max (max Cg₁ Cgc) 1000, by linarith, ?_⟩
  intro Cg hCg D L f μsec ka b hμN hL hg4 hf hsec l a ha γ hG
  have g1 : Cg₁ ≤ Cg := le_trans (le_max_of_le_left (le_max_left _ _)) hCg
  have g2 : Cgc ≤ Cg := le_trans (le_max_of_le_left (le_max_right _ _)) hCg
  have g3 : 1000 ≤ Cg := le_trans (le_max_right _ _) hCg
  unfold WIneq
  by_cases h0 : orbSq L f γ = 0
  · simp [h0]
  obtain ⟨hk1, hε, hc, hN0, hNt, hStd, hT1, hT1'⟩ := hL
  have hb2 : 2 ≤ b := by
    have h1 := b_ge_of_StdHyp0 hk1 hStd.to0
    have h2 : (1 : ℝ) ≤ ((2 * D.R.rS + D.R.k + 1 : ℕ) : ℝ) ^ 7 :=
      one_le_pow₀ (by exact_mod_cast (by omega : 1 ≤ 2 * D.R.rS + D.R.k + 1))
    nlinarith
  obtain ⟨hlam, hI, hI', hka, hka1, -, -, -, hTle, hTle', hlamb, hub, hub', -, hgap, ⟨bv, hbv, hshape⟩, hcut⟩ := hStd
  have hk2 : 2 ≤ D.R.k := by have := D.R.two_le_m; have := D.R.m_add_three_le_k; omega
  have hε' : L.ε = PI.BesselPeriodGGP.eps48 D.R.k D.R.rS := by
    rw [hε]
    funext i
    simp [PI.BesselPeriodGGP.eps48, epsSH, epsS]
  clear hε
  rw [one_pow, mul_one] at hT1 hT1'
  have hb1 : 1 ≤ b := by linarith
  have hb0 : 0 < b := by linarith
  have hcStd : L.c = cStd := by rw [hc]; exact Formalism.MainNotions.OnePlaceEstimates.cOfDpsi_one
  have hInCC := hCC D.R.k D.R.rS L f hk1 hf (Formalism.L2.SG.Pf.BesselExpansion.gap_mono hgap
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right g2 (by positivity)) (by positivity)))
  have hok := GapSizes.gapOK_of D.R.k D.R.rS hk1 Cg g3
  rw [mul_assoc] at hgap hok
  have hu := GlobalTheory.BesselMapCompare.isHCParam_of_isHCTypeW (z := L.z) (u := L.u) (π := L.π) L.hπ
  have hu' := GlobalTheory.BesselMapCompare.isHCParam_of_isHCTypeW (z := L.z') (u := L.u') (π := L.π') L.hπ'
  have hTy := hypType_of hk1 hlam hu hI hub
  have hTy' := hypType_of hk1 hlam hu' hI' hub'
  obtain ⟨hcl, hnd⟩ := shape_of hk1 hlam hu hI hshape
  have hPOK : (parOfL L (lamN L.u) (lamN L.u')).OK :=
    Inhab.ok_diff (parOfL L (lamN L.u) (lamN L.u')) hk1 L.hz.2 L.hz'.2 L.lam b hlam hTy hTy'
  have hplace : Formalism.FourierDecayAlt.Q.IsPlace (parOfL L (lamN L.u) (lamN L.u')) L.z L.z' L.π L.π' :=
    ⟨hPOK, L.hz.1, L.hz'.1, rfl, rfl, TypeHC.isType_of_hc L.hz.1 L.hz.2 L.hπ (lamN_succ L.u),
      TypeHC.isType_of_hc L.hz'.1 L.hz'.2 L.hπ' (lamN_succ L.u')⟩
  have hW := Formalism.MainNotions.BridgeLemma₃.hu_haarUp.1 D.R.k D.R.rS L.z L.μW L.hz.1 L.hz.2 L.hμW.1
  have hW' := Formalism.MainNotions.BridgeLemma₃.hu_haarUp.1 D.R.k D.R.rS L.z' L.μW' L.hz'.1 L.hz'.2 L.hμW'.1
  have hfK : Formalism.FourierDecayAlt.P.CutBP.KFinDSCoef (PI.BesselPeriodGGP.eps48 D.R.k D.R.rS) L.lam f := by
    obtain ⟨Pm, Qm, h1, h2, h3⟩ := hf
    exact ⟨L.Hs, _, _, _, L.σ, Pm, Qm, L.hlam, hε' ▸ L.hσ, h1, h2, fun g _ => h3 g⟩
  have hr2 : 36 * ((D.R.rS : ℝ) + 1) ^ 2 ≤ Cg * ((D.R.rS : ℝ) + 1) ^ 2 := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  have hr1 : 1 ≤ ((D.R.rS : ℝ) + 1) ^ 2 := by nlinarith [(Nat.cast_nonneg D.R.rS : (0 : ℝ) ≤ D.R.rS)]
  obtain ⟨pl, ⟨hz, hz', hπ, hπ', hμW, hμN', hμW'⟩, hcase⟩ :
      ∃ pl : Formalism.FourierDecayAlt.KB.Pl (parOfL L (lamN L.u) (lamN L.u')) L.Wp L.Wq, PlTie L pl ∧
        ((30 * ((D.R.rS : ℝ) + 1) ^ 2 + 6 ≤ |lamN L.u pl.l0 - lamN L.u' pl.l0| ∧
          Formalism.FourierDecayAlt.KB.InDDplus2 _ pl.l0 pl.T.base Cb pl.Θ) ∨
        (lamN L.u = lamN L.u' ∧ ∃ l, 1 ≤ l ∧ l < D.R.k ∧
          2 * (30 * ((D.R.rS : ℝ) + 1) ^ 2 + 6) + 1 ≤ lamN L.u l - lamN L.u (l + 1))) := by
    rcases hcut with ⟨huu, i, hi, hposition, -⟩ | ⟨-, x, y, ⟨i, x', y', -, hxy, hIcc, hx, hy, -⟩, hlen⟩
    · obtain ⟨p, -, e1, e2, e3, e4, e5, e6, e7, -⟩ := hPl L.Wp L.Wq (parOfL L (lamN L.u) (lamN L.u')) L.z L.z' L.π
        L.π' L.μW L.μW' 1 hplace hk2 le_rfl hk1 hW L.hμW.2 hW' L.hμW'.2
      refine ⟨p, ⟨e1, e2, e3, e4, e5, e6.trans hμN.symm, e7⟩, Or.inr ⟨congrArg lamN huu, i + 1, by omega, hi, ?_⟩⟩
      rw [lamN_succ L.u ⟨i, by omega⟩, lamN_succ L.u ⟨i + 1, hi⟩]
      linarith only [hposition, hr1, hr2]
    · obtain ⟨p, e0, e1, e2, e3, e4, e5, e6, e7, hDD⟩ := hPl L.Wp L.Wq (parOfL L (lamN L.u) (lamN L.u')) L.z L.z' L.π
        L.π' L.μW L.μW' (i + 1) hplace hk2 (by omega) i.isLt hW L.hμW.2 hW' L.hμW'.2
      refine ⟨p, ⟨e1, e2, e3, e4, e5, e6.trans hμN.symm, e7⟩, Or.inl ⟨?_, hDD⟩⟩
      rw [e0, lamN_succ L.u i, lamN_succ L.u' i]
      have hxy0 : x ≤ y := by linarith only [hlen, hr1, hr2]
      have h1 : x ∈ Set.Icc x' y' := hIcc ▸ ⟨le_rfl, hxy0⟩
      have h2 : y ∈ Set.Icc x' y' := hIcc ▸ ⟨hxy0, le_rfl⟩
      have h3 := max_sub_min_eq_abs (-L.u i) (-L.u' i)
      rw [show -L.u' i - -L.u i = L.u i - L.u' i by ring] at h3
      linarith only [h1.1, h2.2, hx, hy, h3, hlen, hr1, hr2]
  obtain ⟨g, hg⟩ := exists_relrep L f γ h0
  have hG0 := GPoint_nonneg_of_rep L γ g hg.1
  have hGpos : 0 < Gpt (Tz D.R.k D.R.rS L.z) (Tz D.R.k D.R.rS L.z') γ := lt_of_le_of_ne hG0 (Ne.symm hG)
  have hloc := isLocPt_swap γ
  have hTT : Formalism.FourierDecayAlt.TBB.TTp pl = Tz D.R.k D.R.rS L.z * Tz D.R.k D.R.rS L.z' := by
    unfold Formalism.FourierDecayAlt.TBB.TTp; rw [hz, hz']; rfl
  have hGeq : Formalism.FourierDecayAlt.TBB.Gp pl (γ.1.map Prod.swap) = Gpt (Tz D.R.k D.R.rS L.z) (Tz D.R.k D.R.rS L.z') γ := by
    unfold Formalism.FourierDecayAlt.TBB.Gp; rw [hTT]; exact ptG_eq_GPoint _ _ γ
  have hB := H Cg g1 (parOfL L (lamN L.u) (lamN L.u')) L.Wp L.Wq pl f L.lam b bv l (Nat.le_of_lt_succ l.isLt) a hfK
    hTy hTy' hcl hnd hlamb hbv (fun s s' h => gap_of_lt hlam hg4 h) (hε' ▸ hgap) hok hT1 hT1'
    (scaled_le D.R.rS hb1 hka hka1 hTle) (scaled_le D.R.rS hb1 hka hka1 hTle') hcase ha _ hloc (by rw [hGeq]; exact hGpos)
  have hm : MomL.mnr (Nat.le_of_lt_succ l.isLt) (γ.1.map Prod.swap) = Dpt γ l := by
    unfold MomL.mnr Dpt leadMinor
    rw [ptMatN_swap]
  have hwt := weightTie D.R.k D.R.rS (Tz D.R.k D.R.rS L.z) (Tz D.R.k D.R.rS L.z') γ hk1
  have hn0 : 0 ≤ ptWeight D.R.k D.R.rS (Tz D.R.k D.R.rS L.z) (Tz D.R.k D.R.rS L.z') γ := by
    unfold ptWeight
    exact ptWeightFrom_nonneg _ _ _ _ _ 0 (fun b hb => (γ.2.1 b hb).2) (by rw [Nat.zero_add]; exact γ.2.2)
      (fun t ht => last_ok_of_G _ _ _ hG0 t ht)
  have hnPt : 0 ≤ Formalism.FourierDecayAlt.TBB.nPt D.R.k D.R.rS (Formalism.FourierDecayAlt.TBB.TTp pl) (γ.1.map Prod.swap) := by
    rw [hTT, ← hwt]; exact hn0
  have hEw : Formalism.FourierDecayAlt.TBB.Ew pl (fun _ => 1) f (D.R.rS + 1) [] (γ.1.map Prod.swap) =
      Formalism.FourierDecayAlt.TBB.nPt D.R.k D.R.rS (Formalism.FourierDecayAlt.TBB.TTp pl) (γ.1.map Prod.swap) *
        (Formalism.FourierDecayAlt.B.hsInner (Formalism.FourierDecayAlt.D.vecV pl.T.base pl.ν' pl.m₀ f (γ.1.map Prod.swap))
          (Formalism.FourierDecayAlt.D.vecV pl.T.base pl.ν' pl.m₀ f (γ.1.map Prod.swap))).re := ew_top pl f (γ.1.map Prod.swap) hloc hnPt
  rw [hTT, ← hwt] at hEw
  have hX := tieTopXk D.R.k D.R.rS hk1 L pl.T.base pl.ν' pl.m₀ hcStd hN0 hNt hz hz' hπ hπ' hμW hμN' hμW' pl.hF f γ
    hf hInCC hGpos ⟨g, hg⟩
  have hJ := Ties.energy_identity D.R.k D.R.rS L f μsec _ _ pl hk1 hcStd hN0 hNt ⟨hz, hz', hπ, hπ', hμW, hμN', hμW'⟩ hf hInCC
    hsec
  have hπb : Real.pi ^ (2 * (2 * D.R.rS + 2) ^ 2) ≤ b ^ (4 * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 5) := by
    have h1 : Real.pi ≤ b ^ 2 := by nlinarith [Real.pi_lt_four]
    refine (pow_le_pow_left₀ Real.pi_pos.le h1 _).trans ?_
    rw [← pow_mul, ← Real.rpow_natCast]
    refine Real.rpow_le_rpow_of_exponent_le hb1 ?_
    have h2 : ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 2 ≤ ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 5 :=
      pow_le_pow_right₀ (by exact_mod_cast (by omega : 1 ≤ 2 * D.R.rS + 2)) (by norm_num)
    push_cast at h2 ⊢
    linarith
  have hpc : Real.pi ^ (2 * Formalism.MainNotions.BigCellDensity.pc D.R.rS (γ.1.map Prod.snd)) ≤ Real.pi ^ (2 * (2 * D.R.rS + 2) ^ 2) := by
    refine pow_le_pow_right₀ (by linarith [Real.pi_gt_three]) ?_
    have := pc_le D.R.rS (γ.1.map Prod.snd)
    nlinarith
  change ENNReal.ofReal (‖MomL.mnr (Nat.le_of_lt_succ l.isLt : (l : ℕ) ≤ D.R.rS) _‖ ^ (2 * a) * Formalism.FourierDecayAlt.TBB.Ew pl _ f (D.R.rS + 1) [] _) ≤
    ENNReal.ofReal (b ^ (C₅ * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 5) * max 1 (1 / Formalism.FourierDecayAlt.TBB.Gp pl _) ^ (40 * (D.R.rS + 1) ^ 2)) *
      Formalism.FourierDecayAlt.TBB.jN2 pl f at hB
  rw [hm, hGeq] at hB
  rw [hEw] at hB
  rw [hX, ← ENNReal.ofReal_mul (mul_nonneg (by positivity) hn0), mul_left_comm, ENNReal.ofReal_mul (by positivity),
    mul_assoc]
  refine (mul_le_mul' (ENNReal.ofReal_le_ofReal (hpc.trans hπb))
    (hB.trans (mul_le_mul' le_rfl (hJ.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal hπb) le_rfl))))).trans (le_of_eq ?_)
  rw [← mul_assoc, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  congr 2
  rw [show (C₅ + 8) * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 5 = 4 * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 5 + C₅ * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 5 +
    4 * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 5 by ring, Real.rpow_add hb0, Real.rpow_add hb0]
  ring

theorem wLoc1_of_N {D : D7} {Ch Cg Ca C : ℝ}
    (H : WLoc1 D Ch Cg Ca C fun L => L.μN = Formalism.FourierDecayAlt.D.muN D.R.k D.R.rS) : WLoc1 D Ch Cg Ca C fun _ => True := by
  intro L f μsec ka b _ hok hg hf hsec l a ha γ hγ
  obtain ⟨c, hc0, hc1, hc⟩ := Formalism.MainNotions.BridgeLemma₃.hu_eq_smul (Formalism.FourierDecayAlt.P.unipotent_radical_closed D.R.k D.R.rS)
    (Formalism.FourierDecayAlt.P.nilpotent_measure_is_haar D.R.k D.R.rS) (Formalism.MainNotions.BridgeCSB.haarLieN D.R.k D.R.rS 1 one_ne_zero ENNReal.one_ne_top)
  have hsm : ∀ κ : ℝ≥0∞, haarLie (Nset D.R.k D.R.rS) κ = κ • haarLie (Nset D.R.k D.R.rS) 1 := fun κ => by
    simp [haarLie]
  have h1 : (Ties.withN L c⁻¹).μN = Formalism.FourierDecayAlt.D.muN D.R.k D.R.rS := by
    change haarLie _ c⁻¹ = _
    rw [hsm, hc, smul_smul, ENNReal.inv_mul_cancel hc0 hc1, one_smul]
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := hok
  have h2 : L.μN = (L.κN * c) • (Ties.withN L c⁻¹).μN := by
    rw [h1, ← smul_smul, ← hc]
    exact hsm _
  have hs0 : L.κN * c ≠ 0 := mul_ne_zero a4.ne' hc0
  have hs1 : L.κN * c ≠ ⊤ := ENNReal.mul_ne_top a5 hc1
  have h3 := Ties.pairMeas_smul L c⁻¹ _ h2
  have hB := H (Ties.withN L c⁻¹) f μsec ka b h1
    ⟨a1, a2, a3, ENNReal.inv_pos.2 hc1, ENNReal.inv_ne_top.2 hc0, a6⟩ hg hf hsec l a ha γ hγ
  unfold WIneq at hB ⊢
  rw [Ties.jNorm2_eq L c⁻¹ _ h3 f μsec]
  calc _ ≤ _ * (_ * orbSq (Ties.withN L c⁻¹) f γ) :=
        mul_le_mul' le_rfl (Ties.orbSq_le L c⁻¹ _ (mul_ne_zero hs0 hs0) (ENNReal.mul_ne_top hs1 hs1) h3 f γ)
    _ = _ * (_ * orbSq (Ties.withN L c⁻¹) f γ) := mul_left_comm _ _ _
    _ ≤ _ * (_ * jNorm2 (Ties.withN L c⁻¹) f μsec) := mul_le_mul' le_rfl hB
    _ = _ := mul_left_comm _ _ _

theorem dpt_le {r : ℕ} {ka B : ℝ} (hka : 0 < ka) (h1 : ka ≤ B) (h2 : ka⁻¹ ≤ B) (hB : 1 ≤ B) (γ : Point ℂ (r + 1))
    (l : Fin (r + 1)) : ‖Dpt γ l‖ ≤ B ^ (2 * r + 2) ^ 2 *
      ‖Dpt (Formalism.MainNotions.FrameBoundFromBesselTorus.ptTr ka⁻¹ (ka ^ r) (inv_pos.2 hka) (pow_pos hka _) γ) l‖ := by
  unfold Dpt
  rw [Formalism.MainNotions.FrameBoundFromBesselTorus.leadMinor_ptTr, norm_mul, Complex.norm_real, Real.norm_eq_abs, ← mul_assoc]
  refine le_mul_of_one_le_left (norm_nonneg _) ?_
  have key : ∀ a : ℕ, 1 ≤ B ^ (4 * r) * Formalism.MainNotions.FrameBoundFromBesselTorus.tF r ka⁻¹ (ka ^ r) a ^ 2 := fun a => by
    unfold Formalism.MainNotions.FrameBoundFromBesselTorus.tF
    have e1 : 1 ≤ B * ka := by
      have := mul_le_mul_of_nonneg_right h2 hka.le
      rwa [inv_mul_cancel₀ hka.ne'] at this
    have e2 : 1 ≤ B * ka⁻¹ := by
      have := mul_le_mul_of_nonneg_right h1 (inv_pos.2 hka).le
      rwa [mul_inv_cancel₀ hka.ne'] at this
    have e3 : 1 ≤ B ^ r * ka⁻¹ ^ (r - a) :=
      (one_le_pow₀ e2 (n := r - a)).trans (by
        rw [mul_pow]
        exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hB (Nat.sub_le _ _)) (by positivity))
    have e4 : 1 ≤ (B * ka) ^ r * (B ^ r * ka⁻¹ ^ (r - a)) := one_le_mul_of_one_le_of_one_le (one_le_pow₀ e1) e3
    calc (1 : ℝ) ≤ ((B * ka) ^ r * (B ^ r * ka⁻¹ ^ (r - a))) ^ 2 := one_le_pow₀ e4
      _ = _ := by ring
  set S := Finset.univ.filter fun a : Fin (r + 1) => a.val < l.val + 1
  have hc : S.card ≤ r + 1 := (Finset.card_filter_le _ _).trans (by simp)
  have h3 : 1 ≤ ∏ a ∈ S, B ^ (4 * r) * Formalism.MainNotions.FrameBoundFromBesselTorus.tF r ka⁻¹ (ka ^ r) a ^ 2 :=
    le_trans (by simp) (Finset.prod_le_prod (f := fun _ => (1 : ℝ)) (fun _ _ => zero_le_one) fun a _ => key a)
  rw [Finset.prod_mul_distrib, Finset.prod_const, ← pow_mul] at h3
  refine h3.trans (mul_le_mul (pow_le_pow_right₀ hB ?_) (le_abs_self _)
    (Finset.prod_nonneg fun _ _ => sq_nonneg _) (by positivity))
  nlinarith

theorem w_in_frame {D : D7} {Ch Cg Cgf Ca C : ℝ} (hFr : FrameBesselBound D Cgf 2) (H : WLoc1 D Ch Cg Ca C fun _ => True)
    (L : LocBessel D.R.k D.R.rS) (f : Mx D.R.k D.R.rS → (L.Wq →L[ℂ] L.Wp))
    (μsec : ℂ → Matrix (Fin (D.R.k + 1)) (Fin (D.R.k + 1)) ℂ) (ka b : ℝ) (hL : LocOk D Ch Cg L L.lam ka b ka)
    (hg4 : AllGaps L.lam (Cg * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 4)) (hgap : GapFr D Cgf L.ε L.lam) (hB1 : 1 ≤ b ^ Ch)
    (hf : IsKFinCoefH L.σ f) (hsec : IsSection D.R.k D.R.rS L.z L.z' μsec) (l : Fin (D.R.rS + 1)) (a : ℕ)
    (ha : (a : ℝ) ≤ Ca * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 3) (γ : Point ℂ (D.R.rS + 1))
    (hG : Gpt (Tz D.R.k D.R.rS L.z) (Tz D.R.k D.R.rS L.z') γ ≠ 0) :
    WIneq L f μsec γ (‖Dpt γ l‖ ^ (2 * a)) (((b ^ Ch) ^ (2 * D.R.rS + 2) ^ 2) ^ (2 * a) * (FrC D 2 ka *
      (b ^ (C * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 5) * max 1 (1 / (GsC D ka * Gpt (Tz D.R.k D.R.rS L.z) (Tz D.R.k D.R.rS L.z') γ)) ^
        (40 * (D.R.rS + 1) ^ 2)))) := by
  obtain ⟨hk, hε, hc, hκ0, hκt, hStd, hT1, hT1'⟩ := hL
  have hka : 0 < ka := hStd.2.2.2.1
  have hτ : 0 < ka ^ D.R.rS := pow_pos hka _
  obtain ⟨L₁, f₁, e1, e2, e3, e4, e5, e6, e7, e8, e9, hf₁, hrest⟩ :=
    hFr L f ka ka⁻¹ (ka ^ D.R.rS) hka (inv_pos.2 hka) hτ hc hκ0 hκt hε hgap hf
  obtain ⟨μsec₁, hsec₁, K₁, hK₁, hJ₁, hpt⟩ := hrest μsec hsec
  obtain ⟨γ₁, hγ₁, hG₁, -, hle⟩ := hpt γ hG
  have hγe : γ₁ = Formalism.MainNotions.FrameBoundFromBesselTorus.ptTr ka⁻¹ (ka ^ D.R.rS) (inv_pos.2 hka) hτ γ := Subtype.ext hγ₁
  have hsq : (ka ^ D.R.rS) ^ 2 = ka ^ (2 * D.R.rS) := by rw [← pow_mul, mul_comm]
  have hinv : ka ^ (2 * D.R.rS) * (1 / ka) ^ (2 * D.R.rS) = 1 := by
    rw [← mul_pow, mul_one_div, div_self hka.ne', one_pow]
  have hone : (ka / ka) ^ (2 * D.R.rS) = 1 := by rw [div_self hka.ne', one_pow]
  have hL₁ : LocOk D Ch Cg L₁ L₁.lam ka b 1 := by
    refine ⟨hk, e1.trans hε, ?_, e6, e7, ?_, ?_, ?_⟩
    · rw [e5, inv_mul_cancel₀ hka.ne']
    · rw [e1, e2, e3, e4, e8, e9, hsq]
      have a1 : ka ^ (2 * D.R.rS) * Tz D.R.k D.R.rS L.z * (1 / ka) ^ (2 * D.R.rS) =
          Tz D.R.k D.R.rS L.z * (ka / ka) ^ (2 * D.R.rS) := by
        rw [hone, mul_one, mul_right_comm, hinv, one_mul]
      have a2 : ka ^ (2 * D.R.rS) * Tz D.R.k D.R.rS L.z' * (1 / ka) ^ (2 * D.R.rS) =
          Tz D.R.k D.R.rS L.z' * (ka / ka) ^ (2 * D.R.rS) := by
        rw [hone, mul_one, mul_right_comm, hinv, one_mul]
      rw [a1, a2]
      exact hStd
    · rw [e8, hsq, one_pow, mul_one, mul_comm]; exact hT1
    · rw [e9, hsq, one_pow, mul_one, mul_comm]; exact hT1'
  have hG₁0 : Gpt (Tz D.R.k D.R.rS L₁.z) (Tz D.R.k D.R.rS L₁.z') γ₁ ≠ 0 := by
    rw [hG₁]
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ (inv_ne_zero hka.ne')) (pow_ne_zero _ hτ.ne')) hG
  have hB := H L₁ f₁ μsec₁ ka b trivial hL₁ (e2 ▸ hg4) hf₁ hsec₁ l a ha γ₁ hG₁0
  unfold WIneq at hB ⊢
  rw [hG₁, hJ₁, ENNReal.ofReal_mul (by positivity), mul_assoc] at hB
  have hD : ‖Dpt γ l‖ ^ (2 * a) ≤ ((b ^ Ch) ^ (2 * D.R.rS + 2) ^ 2) ^ (2 * a) * ‖Dpt γ₁ l‖ ^ (2 * a) := by
    rw [← mul_pow, hγe]
    exact pow_le_pow_left₀ (norm_nonneg _) (dpt_le hka hStd.2.2.2.2.1 hStd.2.2.2.2.2.1 hB1 γ l) _
  have hK0 : ENNReal.ofReal K₁ ≠ 0 := (ENNReal.ofReal_pos.2 hK₁).ne'
  have hF0 : 0 ≤ FrC D 2 ka := FrC_nonneg D 2 ka hka
  have hX0 : (0 : ℝ) ≤ ((b ^ Ch) ^ (2 * D.R.rS + 2) ^ 2) ^ (2 * a) := by positivity
  rw [← ENNReal.mul_le_mul_iff_right hK0 ENNReal.ofReal_ne_top, ENNReal.ofReal_mul (by positivity), mul_assoc,
    mul_left_comm]
  refine (mul_le_mul' (ENNReal.ofReal_le_ofReal hD) hle).trans ?_
  rw [ENNReal.ofReal_mul hX0, mul_assoc, mul_left_comm (ENNReal.ofReal (‖Dpt γ₁ l‖ ^ (2 * a)))]
  refine (mul_le_mul' le_rfl (mul_le_mul' le_rfl hB)).trans (le_of_eq ?_)
  rw [ENNReal.ofReal_mul hX0, ENNReal.ofReal_mul hF0]
  unfold FrC GsC
  ring

theorem weight_le {ι : Type} [Fintype ι] [Nonempty ι] (s x : ι → ℝ) (N : ι → ℕ) (σ : ℝ) (hσ : 1 ≤ σ)
    (hs0 : ∀ l, 0 ≤ s l) (hs : ∀ l, s l ≤ σ) :
    ∃ (l : ι) (a : ℕ), a ≤ 2 * ∑ l, N l ∧ (∏ l, (1 + s l * x l ^ 2) ^ N l) ^ 2 ≤ (2 * σ) ^ (2 * ∑ l, N l) * x l ^ (2 * a) := by
  obtain ⟨l, -, hl⟩ := Finset.exists_max_image Finset.univ (fun l => x l ^ 2) Finset.univ_nonempty
  have key : ∀ M : ℝ, 1 ≤ M → x l ^ 2 ≤ M → (∏ i, (1 + s i * x i ^ 2) ^ N i) ^ 2 ≤ (2 * σ * M) ^ (2 * ∑ i, N i) := by
    intro M hM hx
    rw [mul_comm 2 (∑ i, N i), pow_mul, ← Finset.prod_pow_eq_pow_sum]
    have hn : ∀ i, 0 ≤ 1 + s i * x i ^ 2 := fun i => add_nonneg zero_le_one (mul_nonneg (hs0 i) (sq_nonneg _))
    refine pow_le_pow_left₀ (Finset.prod_nonneg fun i _ => pow_nonneg (hn i) _)
      (Finset.prod_le_prod (fun i _ => pow_nonneg (hn i) _) fun i _ => pow_le_pow_left₀ (hn i) ?_ _) 2
    have h1 : s i * x i ^ 2 ≤ σ * M := mul_le_mul (hs i) ((hl i (Finset.mem_univ _)).trans hx) (sq_nonneg _) (by linarith)
    have h2 : 1 ≤ σ * M := one_le_mul_of_one_le_of_one_le hσ hM
    linarith
  rcases le_total (x l ^ 2) 1 with h | h
  · exact ⟨l, 0, Nat.zero_le _, by simpa using key 1 le_rfl h⟩
  · refine ⟨l, _, le_rfl, (key _ h le_rfl).trans (le_of_eq ?_)⟩
    rw [mul_pow (2 * σ), ← pow_mul]

set_option maxHeartbeats 1600000 in

theorem weighted_uniform_rotated_of_expansion_alt_alt (hW : ∀ Cb, WEnd.WBp Cb) {Cgc Cgf : ℝ} (hCC : CoefCC1 Cgc)
    (hOB : ∀ D : D7, Formalism.MainNotions.FrameBoundFromBesselTorus.OneBesselTor D Cgf) : Formalism.MainNotions.RotatedPoints.WeightedBoundRotatedUniform := by
  intro Aw Ch hAw
  obtain ⟨C, Cg₀, hC, H⟩ := wLoc1N_of hW hCC Ch (2 * (1 + Aw + 10))
  refine ⟨((4 + |Ch|) * (2 * (1 + Aw + 10)) + |Ch| * (4 * (1 + Aw + 10)) + 4 * |Ch| + C + (3 + 3 * |Ch|) * 10) + 6,
    max (max Cg₀ Cgf) 2, fun Cg hCg0 D => ?_⟩
  have g1 : Cg₀ ≤ Cg := le_trans (le_max_of_le_left (le_max_left _ _)) hCg0
  have g2 : Cgf ≤ Cg := le_trans (le_max_of_le_left (le_max_right _ _)) hCg0
  have hCg : 2 ≤ Cg := le_trans (le_max_right _ _) hCg0
  have hFr := Formalism.MainNotions.OnePlaceExpansion.frame_bound_of_bessel_torus D Cgf 2 le_rfl (hOB D)
  have H1 := wLoc1_of_N (H Cg g1 D)
  refine Formalism.MainNotions.RotatedPoints.weighted_bound_rotated_of_one_place (A := AQ D 10) hCg ?_
  intro T T' b X hP γ hγ v
  set A := AQ D 10 with hAd
  set p : ℝ := Aw * ((D.R.rS : ℝ) + 1) ^ 2 with hpd
  have hp : 0 ≤ p := by positivity
  by_cases hO : orbSq (X.L v) (X.f v) (Pv.Frames.turnPt (ptLoc D v γ)) = 0
  · rw [hO, mul_zero]; exact bot_le
  have hL := X.hL v
  obtain ⟨hk, -, -, -, -, hStd, -, -⟩ := id hL
  have hb2 : 2 ≤ b := by
    have h1 := b_ge_of_StdHyp0 hk hStd.to0
    have h2 : (1 : ℝ) ≤ ((2 * D.R.rS + D.R.k + 1 : ℕ) : ℝ) ^ 7 :=
      one_le_pow₀ (by exact_mod_cast (by omega : 1 ≤ 2 * D.R.rS + D.R.k + 1))
    nlinarith
  have hb1 : 1 ≤ b := by linarith
  have hka : 0 < kaRe D := hStd.2.2.2.1
  have hk1 : kaRe D ≤ b ^ Ch := hStd.2.2.2.2.1
  have hk2 : (kaRe D)⁻¹ ≤ b ^ Ch := hStd.2.2.2.2.2.1
  set xG : ℝ := Complex.normSq (plEmb D v (leadMinorK (ptMat γ) (D.R.rS + 1) le_rfl)) -
    (T : ℝ) * (T' : ℝ) * Complex.normSq (plEmb D v (leadMinorK (ptMat γ) D.R.rS (Nat.le_succ _))) with hxGd
  have hxG : plEmb D v (Gglob D T T' γ) = (xG : ℂ) := plEmb_Gglob D T T' v γ
  have hxG0 : xG ≠ 0 := by
    intro h0
    have : plEmb D v (Gglob D T T' γ) = 0 := by rw [hxG, h0]; simp
    exact hγ.2.1 ((map_eq_zero (plEmb D v)).1 this)
  have habs : absV D v (Gglob D T T' γ) = |xG| := by
    unfold absV; rw [hxG, Complex.norm_real, Real.norm_eq_abs]
  have hGreal : Gpt (T : ℝ) (T' : ℝ) (ptLoc D v γ) = ((∏ i : Fin D.R.rS, alf D i) ^ 2) ^ 2 * xG :=
    GPoint_loc D T T' v γ
  have ha4 : 0 < ((∏ i : Fin D.R.rS, alf D i) ^ 2) ^ 2 := by
    have := Finset.prod_pos (s := Finset.univ) (fun (i : Fin D.R.rS) _ => alf_pos D i)
    positivity
  have hGne : Gpt (Tz D.R.k D.R.rS (X.L v).z) (Tz D.R.k D.R.rS (X.L v).z') (Pv.Frames.turnPt (ptLoc D v γ)) ≠ 0 := by
    rw [Pv.Frames.GPoint_turnPt, (X.hT v).1, (X.hT v).2, hGreal]
    exact mul_ne_zero ha4.ne' hxG0
  obtain ⟨g, hg⟩ := exists_rep_of_orbSq _ _ _ hO
  have hGnn := GPoint_nonneg_of_rep _ _ g hg
  rw [Pv.Frames.GPoint_turnPt, (X.hT v).1, (X.hT v).2] at hGnn
  have hxGnn : 0 ≤ xG := by
    rw [hGreal] at hGnn
    exact nonneg_of_mul_nonneg_right hGnn ha4
  have hGd : absV D v (Gglob D T T' γ) ≤ dLoc D v γ := by
    rw [habs, abs_of_nonneg hxGnn]
    unfold dLoc absV
    rw [← Complex.normSq_eq_norm_sq]
    have : 0 ≤ (T : ℝ) * (T' : ℝ) * Complex.normSq (plEmb D v (leadMinorK (ptMat γ) D.R.rS (Nat.le_succ _))) := by
      have := Complex.normSq_nonneg (plEmb D v (leadMinorK (ptMat γ) D.R.rS (Nat.le_succ _)))
      positivity
    linarith
  have hn0 : 0 ≤ nLoc D T T' v γ := by
    unfold nLoc ptWeight
    exact ptWeightFrom_nonneg _ _ _ _ _ 0 (fun b hb => ((ptLoc D v γ).2.1 b hb).2)
      (by rw [Nat.zero_add]; exact (ptLoc D v γ).2.2)
      (fun t ht => last_ok_of_G _ _ _ hGnn t ht)
  have hb0 : 0 < b := by linarith
  have hCh : 0 ≤ Ch := ch_nonneg hCg ⟨X.hL v, X.hnear v, X.hcoef v, X.hsec v, X.hT v⟩
  rw [abs_of_nonneg hCh]
  have hlam := lam_eq_of_dist0 D X v
  have hgF : GapFr D Cgf (X.L v).ε (X.L v).lam := by
    rw [hlam]
    exact Formalism.L2.SG.Pf.BesselExpansion.gap_mono hStd.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right g2 (by positivity)) (by positivity))
  set M : ℝ := ((2 * D.R.rS + 2 : ℕ) : ℝ) with hM
  have hM1 : 1 ≤ M := by rw [hM]; exact_mod_cast (by omega : 1 ≤ 2 * D.R.rS + 2)
  have hσ1 : 1 ≤ b ^ ((3 + Ch) * M ^ 2) := Real.one_le_rpow hb1 (by positivity)
  obtain ⟨l, a, ha, hwt⟩ := weight_le (sQ D) (fun l => ‖Dpt (ptLoc D v γ) l‖) (Formalism.MainNotions.TheoremBConstants.NQ D A p) _ hσ1 (sQ_nonneg D)
    fun l => alfProd_inv_le_b D Ch b hCh hb2 hka hk2 _ (by omega)
  simp only [Fl_eq] at hwt
  have hSN := sum_weighted_point_counts_le_cube D Aw 10 hAw (by norm_num)
  have hS2 : ((2 * ∑ l, Formalism.MainNotions.TheoremBConstants.NQ D A p l : ℕ) : ℝ) ≤ 2 * (1 + Aw + 10) * M ^ 3 := by
    rw [Nat.cast_mul, Nat.cast_ofNat]
    have : ((∑ l, Formalism.MainNotions.TheoremBConstants.NQ D A p l : ℕ) : ℝ) ≤ (1 + Aw + 10) * M ^ 3 := hSN
    linarith only [this]
  have ha' : (a : ℝ) ≤ 2 * (1 + Aw + 10) * M ^ 3 := le_trans (by exact_mod_cast ha) hS2
  have hloc := w_in_frame hFr H1 (X.L v) (X.f v) (X.μsec v) (kaRe D) b (hlam ▸ hL) (hP v) hgF
    (Real.one_le_rpow hb1 hCh) (X.hcoef v) (X.hsec v) l a ha' (Pv.Frames.turnPt (ptLoc D v γ)) hGne
  unfold WIneq at hloc
  simp only [Dpt_norm_turnPt, Pv.Frames.ptWeight_turnPt, Pv.Frames.GPoint_turnPt] at hloc
  rw [(X.hT v).1, (X.hT v).2, hGreal] at hloc
  have hw := weights_le D T T' v γ A p hp hGd
  have h1 : wLoc D v γ ^ 2 * (1 + dLoc D v γ) ^ A * nLoc D T T' v γ * WLoc D T T' v γ ^ p ≤
      (∏ l, Fl D v γ l ^ Formalism.MainNotions.TheoremBConstants.NQ D A p l) ^ 2 * nLoc D T T' v γ := by
    calc wLoc D v γ ^ 2 * (1 + dLoc D v γ) ^ A * nLoc D T T' v γ * WLoc D T T' v γ ^ p
        = (wLoc D v γ ^ 2 * (1 + dLoc D v γ) ^ A * WLoc D T T' v γ ^ p) * nLoc D T T' v γ := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hw hn0
  have hY0 : 0 ≤ (2 * b ^ ((3 + Ch) * M ^ 2)) ^ (2 * ∑ l, Formalism.MainNotions.TheoremBConstants.NQ D A p l) := by positivity
  have h2 := h1.trans ((mul_le_mul_of_nonneg_right hwt hn0).trans (le_of_eq (mul_assoc _ _ _)))
  refine (mul_le_mul' (ENNReal.ofReal_le_ofReal h2) le_rfl).trans ?_
  rw [ENNReal.ofReal_mul hY0, mul_assoc]
  refine (mul_le_mul' le_rfl hloc).trans ?_
  rw [← mul_assoc, ← ENNReal.ofReal_mul hY0]
  refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
  have hM25 : M ^ 2 ≤ M ^ 5 := pow_le_pow_right₀ hM1 (by norm_num)
  have hM45 : M ^ 4 ≤ M ^ 5 := pow_le_pow_right₀ hM1 (by norm_num)
  have hM2 : 1 ≤ M ^ 2 := one_le_pow₀ hM1
  have n1 : (2 * b ^ ((3 + Ch) * M ^ 2)) ^ (2 * ∑ l, Formalism.MainNotions.TheoremBConstants.NQ D A p l) ≤ b ^ ((4 + Ch) * (2 * (1 + Aw + 10)) * M ^ 5) := by
    have e1 : 2 * b ^ ((3 + Ch) * M ^ 2) ≤ b ^ ((4 + Ch) * M ^ 2) := by
      rw [show (4 + Ch) * M ^ 2 = M ^ 2 + (3 + Ch) * M ^ 2 by ring, Real.rpow_add hb0]
      refine mul_le_mul_of_nonneg_right (hb2.trans ?_) (by positivity)
      simpa using bp_mono hb1 hM2
    refine (bp_pow hb0 e1 (by positivity) _).trans (bp_mono hb1 ?_)
    calc _ ≤ (4 + Ch) * M ^ 2 * (2 * (1 + Aw + 10) * M ^ 3) := mul_le_mul_of_nonneg_left hS2 (by positivity)
      _ = _ := by ring
  have n2 : ((b ^ Ch) ^ (2 * D.R.rS + 2) ^ 2) ^ (2 * a) ≤ b ^ (Ch * (4 * (1 + Aw + 10)) * M ^ 5) := by
    refine (bp_pow hb0 (bp_pow hb0 le_rfl (by positivity) _) (by positivity) _).trans (bp_mono hb1 ?_)
    rw [Nat.cast_pow, ← hM, Nat.cast_mul, Nat.cast_ofNat]
    calc _ ≤ Ch * M ^ 2 * (2 * (2 * (1 + Aw + 10) * M ^ 3)) :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = _ := by ring
  have n3 : FrC D 2 (kaRe D) ≤ b ^ (4 * Ch * M ^ 5) :=
    (num_Fr D Ch 2 b (kaRe D) hCh (by norm_num) hb2 hka hk1 hk2).trans
      (bp_mono hb1 (by nlinarith [mul_le_mul_of_nonneg_left hM25 hCh]))
  have n4 := num_G D Ch 10 b hCh (by norm_num) hb2 hka hk1 hk2 A (AQ_ge D 10) xG hxG0
  rw [show 10 * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 2 = ((40 * (D.R.rS + 1) ^ 2 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast,
    show ((40 * (D.R.rS + 1) ^ 2 : ℕ) : ℝ) = 10 * M ^ 2 by rw [hM]; push_cast; ring] at n4
  have n5 : b ^ ((3 + 3 * Ch) * M ^ 2 * (10 * M ^ 2)) ≤ b ^ ((3 + 3 * Ch) * 10 * M ^ 5) :=
    bp_mono hb1 (by nlinarith [mul_le_mul_of_nonneg_left hM45 (show 0 ≤ (3 + 3 * Ch) * 10 by positivity)])
  have n6 := n4.trans (mul_le_mul_of_nonneg_right n5 (by positivity))
  have hF0 := FrC_nonneg D 2 (kaRe D) hka
  rw [habs, add_mul _ _ (M ^ 5), add_mul _ _ (M ^ 5), add_mul _ _ (M ^ 5), add_mul _ _ (M ^ 5), Real.rpow_add hb0, Real.rpow_add hb0, Real.rpow_add hb0,
    Real.rpow_add hb0]
  calc _ ≤ b ^ ((4 + Ch) * (2 * (1 + Aw + 10)) * M ^ 5) * (b ^ (Ch * (4 * (1 + Aw + 10)) * M ^ 5) *
        (b ^ (4 * Ch * M ^ 5) * (b ^ (C * M ^ 5) * (b ^ ((3 + 3 * Ch) * 10 * M ^ 5) * max 1 (1 / |xG|) ^ A)))) := by
        gcongr
    _ = _ := by ring

end CompanionTheory.WaveGrid.WGlue
