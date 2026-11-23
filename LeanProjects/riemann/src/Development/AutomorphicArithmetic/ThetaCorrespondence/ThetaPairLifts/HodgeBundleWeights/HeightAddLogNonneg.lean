import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.TamagawaNumberSpecialUnitary
import Development.WeilBound.CoreStatements.NefModelVolumes.TwoLtHalfFinrank
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.VolumeEstimateHypotheses
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ToKnownTheoremsOf
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.CoverHeightComparison
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.VolumeLineBundleLe
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ImageHeightNonnegOfDivisor

section
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
noncomputable section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.CovHt
namespace GlobalTheory.CovHt.HtTopG
section Point
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} {p : PtAt ex Csz} {i : Fin D.R.m} {Y : Cov p i}
theorem height_add_log_nonneg (hP : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems) {u1 : AllWt.Weight (dat p i)} {Z : Comp Y.d.Xo₂ Y.d.c₂} {n : ℕ}
    {w : Fin n → cuspOn Y.U Z (wtOf (dat p i) u1 0)} {abelian₂ : ℝ}
    (hw : IsShortGen (normOn Y.U (xiR D) (fun _ => D.sp.W ((i : ℕ) + 1)) Y.dict Z (wtOf (dat p i) u1 0))
        (latOn Y.U Z (wtOf (dat p i) u1 0)) w abelian₂)
    (hG : GoodOn Y.U (xiR D) (fun _ => D.sp.W ((i : ℕ) + 1)) Y.dict Z (wtOf (dat p i) u1 0)) (hd : 0 < Y.dg u1 Z) :
    0 ≤ Y.ht u1 Z + Real.log abelian₂ := by
  haveI hTC : IsTotallyComplex Y.d.c₂.F := ⟨fun v => by
    rw [← InfinitePlace.not_isReal_iff_isComplex, InfinitePlace.isReal_iff, ComplexEmbedding.isReal_iff]
    exact fun e => GlobalTheory.CompHt.conj_comp_ne (c := Y.d.c₂) v.embedding (RingHom.ext fun a => RingHom.congr_fun e a)⟩
  have hd' : 0 < compDeg Y.U Z (wtOf (dat p i) u1 0) := by exact_mod_cast hd
  exact _root_.GlobalTheory.ImageHeightNonneg.imageHeight_nonneg_of_divisor hP _ _ _ _ _ _ _ _ w abelian₂ hG.1 (fun σ f => petOn_conj _ _ _ _ Z _ σ f) hG.2.2 hw hd'
theorem slope_le_height (hPX : _root_.SelfIntersectionVolumeEstimates.VolumeEstimateHypotheses) (hP : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems) {e : ℕ} {o : ℝ} (hY : Y.Good e o) (hHT : HTCmp Y.d.Xo₂ Y.d.c₂)
    {u1 : AllWt.Weight (dat p i)} {Z : Comp Y.d.Xo₂ Y.d.c₂} {n : ℕ}
    {w : Fin n → cuspOn Y.U Z (wtOf (dat p i) u1 0)} {abelian₂ : ℝ}
    (hw : IsShortGen (normOn Y.U (xiR D) (fun _ => D.sp.W ((i : ℕ) + 1)) Y.dict Z (wtOf (dat p i) u1 0))
        (latOn Y.U Z (wtOf (dat p i) u1 0)) w abelian₂)
    (hGo : GoodOn Y.U (xiR D) (fun _ => D.sp.W ((i : ℕ) + 1)) Y.dict Z (wtOf (dat p i) u1 0))
    (hBir : GlobalTheory.DegVal.BirOn Y.U Z (wtOf (dat p i) u1 0))
    (hdel : (1 - rhoB (dat p i) u1) * Y.dg u1 Z ≤ delPrime Y.U Z u1) (hρ : rhoB (dat p i) u1 < 1) (hd : 0 < Y.dg u1 Z)
    {cc B s cs : ℝ} (hM : Mult Y.U (xiR D) (fun _ => D.sp.W ((i : ℕ) + 1)) Y.dict Z u1 (uPrime (dat p i) u1) cc)
    (hcc : 0 ≤ cc) (hh : 0 ≤ htCost Y.d.l₂ B * l1 (uPrime (dat p i) u1)) (hcs : Real.log abelian₂ ≤ cs)
    (hnn : 0 ≤ Y.ht u1 Z + cs)
    (hs : (s : EReal) ≤ compVolSlope Y.U (xiR D) 8 (mixVals Y.d.Xo₂ Y.d.c₂ B) Z (uPrime (dat p i) u1)) :
    (1 - rhoB (dat p i) u1) * max 0 (s + cs) ≤ Y.ht u1 Z + cs + (cc + htCost Y.d.l₂ B * l1 (uPrime (dat p i) u1)) := by
  have h1ρ : 0 < 1 - rhoB (dat p i) u1 := by linarith
  have hdelpos : 0 < topDeg Y.U Z (uPrime (dat p i) u1) :=
    lt_of_lt_of_le (mul_pos h1ρ hd) hdel
  have hf := two_lt_half_finrank D
  set hc := htCost Y.d.l₂ B * l1 (uPrime (dat p i) u1) with hhc
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have hA := (le_compVolSlope_iff Y.U (xiR D) 8 (mixVals Y.d.Xo₂ Y.d.c₂ B) hdelpos s).1 hs cs
  have hB := GlobalTheory.CovHtCmp.compVol_le_volL_deep D p.T.toCore ((i : ℕ) + 1) Y e o hY hf hHT Z u1 (uPrime (dat p i) u1) cc B cs ε hM hε
  have hC := _root_.SelfIntersectionVolumeEstimates.VolUpG.volume_line_bundle_le hPX hP D p.T.toCore ((i : ℕ) + 1) Y e o hY hf Z u1 n w abelian₂ (cs + cc + hc + ε) hGo hBir hM.1 hd hw
    (by linarith)
  have hABC := hA.trans (hB.trans hC)
  have hpos : 0 ≤ Y.dg u1 Z * (Y.ht u1 Z + (cs + cc + hc + ε)) := mul_nonneg hd.le (by linarith)
  rw [ENNReal.ofReal_le_ofReal_iff hpos] at hABC
  change delPrime Y.U Z u1 * (s + cs) ≤ _ at hABC
  have key : (1 - rhoB (dat p i) u1) * max 0 (s + cs) * Y.dg u1 Z ≤ (Y.ht u1 Z + cs + (cc + hc) + ε) * Y.dg u1 Z := by
    rcases le_total (s + cs) 0 with h | h
    · rw [max_eq_left h, mul_zero, zero_mul]
      exact mul_nonneg (by linarith) hd.le
    · rw [max_eq_right h]
      calc (1 - rhoB (dat p i) u1) * (s + cs) * Y.dg u1 Z = ((1 - rhoB (dat p i) u1) * Y.dg u1 Z) * (s + cs) := by ring
        _ ≤ delPrime Y.U Z u1 * (s + cs) := mul_le_mul_of_nonneg_right hdel h
        _ ≤ _ := hABC
        _ = _ := by ring
  exact le_of_mul_le_mul_right key hd
theorem heightAt_eq_of_cover (hPX : _root_.SelfIntersectionVolumeEstimates.VolumeEstimateHypotheses) (hP : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems) {e : ℕ} {o : ℝ} (hY : Y.Good e o) (hHT : HTCmp Y.d.Xo₂ Y.d.c₂)
    {C0 Cs Cm Cb PP : ℝ} (h0 : 0 ≤ C0) (hs0 : 0 ≤ Cs) (hm0 : 0 ≤ Cm) (hb0 : 0 ≤ Cb) (hU : 0 ≤ unitE p)
    (hmean : MeanAll Y.U (xiR D) (ell D) C0) (hne : Nonempty (Comp Y.d.Xo₂ Y.d.c₂)) {u1 : AllWt.Weight (dat p i)}
    (hρ : rhoB (dat p i) u1 < 1) (hDeg : DegAt p i Y u1) (hS : ShortAt p i Y PP Cs u1) (hGe : GeomAt p i Y u1)
    (hM : MultAt p i Y PP Cm u1) (hB : BudgetAt p i Y PP Cb u1) :
    HeightAt p i Y PP (Cs + Cm + Cb + C0 * Cb) u1 := by
  obtain ⟨abelian₂, hLam, hSb⟩ := hS
  obtain ⟨cc, hcc, hccb, hMZ⟩ := hM
  obtain ⟨-, g, hgap, herr0, herrb, hht0, hhtb⟩ := hB
  obtain ⟨sl, hsl, hX⟩ := hmean (uPrime (dat p i) u1) g hgap
  obtain ⟨δ, hδ, hδZ⟩ := hDeg
  have hdg : ∀ Z, 0 < Y.dg u1 Z := fun Z => lt_of_lt_of_le hδ (hδZ Z).1
  have hLam1 : 1 ≤ abelian₂ := by
    obtain ⟨Z⟩ := hne
    obtain ⟨n, w, hw⟩ := hLam Z
    exact hw.one_le
  have hcs : 0 ≤ Real.log abelian₂ := Real.log_nonneg hLam1
  have hl1 : 0 ≤ l1 (uPrime (dat p i) u1) :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hhc : 0 ≤ htCost Y.d.l₂ (bndB (uPrime (dat p i) u1) g) * l1 (uPrime (dat p i) u1) := mul_nonneg hht0 hl1
  have hT : (0 : ℝ) ≤ lenT p i PP := Nat.cast_nonneg _
  have hnn : ∀ Z, 0 ≤ Y.ht u1 Z + Real.log abelian₂ := fun Z => by
    obtain ⟨n, w, hw⟩ := hLam Z
    exact _root_.GlobalTheory.CovHt.HtTopG.height_add_log_nonneg hP hw (hGe Z).1 (hdg Z)
  have e1 : 0 ≤ Cs * unitE p := mul_nonneg hs0 hU
  have e2 : 0 ≤ Cm * unitE p := mul_nonneg hm0 hU
  have e3 : 0 ≤ Cb * unitE p := mul_nonneg hb0 hU
  have e4 : 0 ≤ C0 * Cb * unitE p := mul_nonneg (mul_nonneg h0 hb0) hU
  refine ⟨Real.log abelian₂, cc + htCost Y.d.l₂ (bndB (uPrime (dat p i) u1) g) * l1 (uPrime (dat p i) u1),
    C0 * errX (ell D) (uPrime (dat p i) u1) g, sl, hcs, add_nonneg hcc hhc, mul_nonneg h0 herr0, hnn, fun Z => ?_, hX,
    ?_, ?_, ?_⟩
  · obtain ⟨n, w, hw⟩ := hLam Z
    exact _root_.GlobalTheory.CovHt.HtTopG.slope_le_height hPX hP hY hHT hw (hGe Z).1 (hGe Z).2.1 (hGe Z).2.2 hρ (hdg Z) (hMZ Z) hcc hhc le_rfl (hnn Z) (hsl Z)
  · have : (lenT p i PP : ℝ) * (C0 * errX (ell D) (uPrime (dat p i) u1) g) ≤ C0 * Cb * unitE p := by
      rw [mul_left_comm, mul_assoc]
      exact mul_le_mul_of_nonneg_left herrb h0
    linarith
  · rw [mul_add]
    linarith
  · linarith
end Point
theorem height_of_geom_multC_budget_meanAll : _root_.SelfIntersectionVolumeEstimates.VolumeEstimateHypotheses → _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → DeepGood → Size → Deg → Short → Geom → MultC → Budget →
    (∃ C : ℝ, 0 ≤ C ∧ ∀ (D : D7) (T : CoreJ D), LawsJ T → D.R.m ^ 2 ≤ D.R.k → ∀ j : ℕ, 1 ≤ j → j < D.R.m → ∀ (Y : Deep T.toCore j) (e : ℕ) (o : ℝ), Y.Good e o → Y.d.l₂.M'.primeFactors.card ≤ 15 → MeanAll Y.U (xiR D) (ell D) C) →
    Height := by
  intro hPX hP hDG hSz hDg hSh hGe hMu hBu hDS
  obtain ⟨C0, h0, hDS⟩ := hDS
  refine Closed.imp ((((((hDG.and hSz).and hDg).and hSh).and hGe).and hMu).and hBu) ?_
  intro eps Fm CH _ hF
  obtain ⟨⟨⟨⟨⟨⟨⟨C1, -, a1⟩, ⟨C2, -, a2⟩⟩, ⟨C3, -, a3⟩⟩, ⟨C4, c4, a4⟩⟩, ⟨C5, -, a5⟩⟩, ⟨C6, c6, a6⟩⟩, ⟨C7, c7, a7⟩⟩ := hF
  refine ⟨C4 + C6 + C7 + C0 * C7, by positivity, ?_⟩
  obtain ⟨x0, hall⟩ := ((((((a1.and a2).and a3).and a4).and a5).and a6).and a7)
  refine ⟨x0, fun x hx hle ι p hp i hm Y hY u1 hq => ?_⟩
  obtain ⟨⟨⟨⟨⟨⟨b1, b2⟩, b3⟩, b4⟩, b5⟩, b6⟩, b7⟩ := hall x hx hle ι p hp
  have hDGa := b1 i hm Y hY
  obtain ⟨hb1, hbE, -, -, -, -, hρ⟩ := b2 i
  have hU : 0 ≤ unitE p := by linarith
  have hρ1 : rhoB (dat p i) u1 < 1 := ((hρ hm).2 u1 hq).2.2.1
  have hBu := b7 i hm Y hY u1 hq
  exact _root_.GlobalTheory.CovHt.HtTopG.heightAt_eq_of_cover hPX hP hY.1 (_root_.GlobalTheory.CovHt.cover_height_comparison hP _ _ _ _ _ _) h0 c4 c6 c7 hU
    (hDS _ p.T p.fw.laws (Formalism.BasicNotions.ParameterChoice'.m_sq_le_k (Fm.params x hx ι)) ((i : ℕ) + 1) (by omega) hm Y _ _ hY.1 hBu.1) hDGa.2.2.2.2.2.2.1 hρ1
    (b3 i hm Y hY u1 hq) (b4 i hm Y hY u1 hq) (b5 i hm Y hY u1 hq) (b6 i hm Y hY u1 hq) hBu
end GlobalTheory.CovHt.HtTopG
end
end
