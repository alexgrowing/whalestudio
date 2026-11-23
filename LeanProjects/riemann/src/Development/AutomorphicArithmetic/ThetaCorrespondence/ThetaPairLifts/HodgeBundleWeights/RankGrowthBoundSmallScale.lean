import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.TamagawaNumberSpecialUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankGrowthBoundSmallScale
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ToKnownTheoremsOf
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ValuationMultiplicityOfConsecutiveRun
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.WeightPrincipalisationBound
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.CoveringTopologyRefinement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ProportionalityPrincipleCompactification
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.CompactificationTopChernEqVolume
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.CoveringDomainLatticeRegularity
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.TwistedFlatBundleRanks
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.JetRankComplexLe
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.UnramifiedPointsAtDeepLevel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankGrowthBoundSmallScaleStatement

section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
noncomputable section
namespace GlobalTheory.CovTop.HodgeSteps
theorem covering_goodAt_shift (hP : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems) (D : D7) (T : CoreJ D) (hL : LawsJ T) (j : ℕ) (hj : InR D j) (Y : Deep T.toCore j) (e : ℕ)
    (o : ℝ) (hY : Y.Good e o) (hpq : 1 ≤ (T.Q.Dw j).p + (T.Q.Dw j).q)
    (hC : GlobalTheory.IndefiniteRowSideFullHecke.ComponentMassSum.IsComplexData Y.U (fun _ => D.sp.W j) Y.dict) (hl : ∀ q : ℕ, q.Prime → Y.d.l₂.GoodAt q)
    (hF : GlobalTheory.FlatLine.FlatExists Y.U (xiR D)) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n kc : ℕ) (s : ℤ) (hn : Even n)
    (h : Y.GoodAt (wtOf _ (uWt (T.Q.Dw j) a n kc + s • hodgeWt (T.Q.Dw j)) 0)) : Y.GoodAt (shiftG (T.Q.Dw j) a n s) := by
  obtain ⟨m, rfl⟩ := hn
  have h1 := (((GlobalTheory.T.flatLine_thetaRoot_twist_twistingSection hP.p5 D T.Q.H (T.Q.Dw j) Y.d.l₂ Y.d.Xo₂ Y.d.c₂ D.R.r Y.U _ Y.dict hC hY.geo hpq hl hF
    (_root_.GlobalTheory.T.unramified_points_of_deep_cover hP D T j Y e o hL hj hY) (anchor (T.Q.Dw j) a (m + m) kc) m).2 _ 0).2 h).1
  have e1 : uWt (T.Q.Dw j) a (m + m) kc + s • hodgeWt (T.Q.Dw j) +
      GlobalTheory.FlatLine.parWt (T.Q.Dw j) (anchor (T.Q.Dw j) a (m + m) kc) =
      laOf (T.Q.Dw j) a (m + m) + s • hodgeWt (T.Q.Dw j) := by
    rw [add_right_comm, uWt_add_anchor]
  rw [e1, add_comm (0 : ℤ), AllWt.wtOf_add] at h1
  have e2 : exZ (T.Q.Dw j) (wtOf (T.Q.Dw j) (laOf (T.Q.Dw j) a (m + m)) m + wtOf (T.Q.Dw j) (s • hodgeWt (T.Q.Dw j)) 0) =
      exZ (T.Q.Dw j) (shiftG (T.Q.Dw j) a (m + m) s) := by
    rw [shiftG, FlatTw.exZ_add_eq, FlatTw.exZ_add_eq]
    congr 1
    have := AllWt.exOf_weightOf (Dw := T.Q.Dw j) (fun x => (a x : ℤ)) m
    rw [AllWt.exOf] at this
    rw [laOf, show (m + m) / 2 = m by omega, this, wtZ]
    push_cast
    rw [two_mul]
  have e3 : cuspW Y.d.Xo₂ Y.d.c₂ Y.U
      (wtOf (T.Q.Dw j) (laOf (T.Q.Dw j) a (m + m)) m + wtOf (T.Q.Dw j) (s • hodgeWt (T.Q.Dw j)) 0) =
      cuspW Y.d.Xo₂ Y.d.c₂ Y.U (shiftG (T.Q.Dw j) a (m + m) s) := by
    ext f
    rw [AllWt.mem_cuspW, AllWt.mem_cuspW, e2]
    exact and_congr_right fun _ => forall₂_congr fun σ hσ => by
      rw [AllWt.modelWt_congr (Y.U σ) hσ (hY.unf σ hσ) e2]
  have key : ∀ C C' : Submodule Y.d.c₂.F (Rul Y.d.Xo₂ Y.d.c₂), C = C' →
      ((AllWt.supLat C).FG ∧ Submodule.span Y.d.c₂.F (AllWt.supLat C : Set C) = ⊤) →
      (AllWt.supLat C').FG ∧ Submodule.span Y.d.c₂.F (AllWt.supLat C' : Set C') = ⊤ := by
    rintro C _ rfl h
    exact h
  exact ⟨hasGram_nrm_of_good D _ j Y e o hY _, key _ _ e3 h1.2⟩
theorem rk_le_one_add_min_mul_rk_neg : GlobalTheory.CovTop.HypothesesX → _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → GlobalTheory.Published.SiegelToroidalIntegral → GlobalTheory.Published.ToroidalForFanKS → GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.HSCore.Quoted → GlobalTheory.Published.SemiAbelianLieSeminegative → DeepGood → Size → FlatDeg → Deg → Share → Covers fun Fm x _ ι p i Y PP _ => ∀ s : ℕ, 1 ≤ s → s ≤ 2 → (Y.rk (Gs p i (s * cZero (Fm.D x ι) ((i : ℕ) + 1))) : ℝ) ≤ (1 + min (1 / 2) ((Fm.L x ι).sc.b / (PP * kap p i))) * Y.rk (Gs p i (-(cZero (Fm.D x ι) ((i : ℕ) + 1)))) := by
  intro hX hP hSi hTo hG hQ hN hDG hS hFD hDeg hSh
  refine ((((((((((hDG.and hS).and hFD).and hDeg).and hSh).and (GlobalTheory.T.weight_parameter_strict_antitone hS)).and (GlobalTheory.T.size_bounds_for_family hS)).and
    (_root_.GlobalTheory.T.valuation_multiplicity_run_estimate hP hG hQ hSi hTo hN hDG hS hFD)).and (GlobalTheory.T.flat_line_c1_log_bound hFD)).and wtBig_run).and WtShape.wtN).imp fun Fm CH _ h => ?_
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨_, -, a1⟩, A, -, a2⟩, _, -, a3⟩, _, -, a4⟩, _, -, a5⟩, _, -, a6⟩, _, -, a7⟩, _, -, a8⟩, _, -, a9⟩,
    _, -, a10⟩, _, -, a11⟩ := h
  obtain ⟨x0, h⟩ := (((((((((a1.and a2).and a3).and a4).and a5).and a6).and a7).and a8).and a9).and a10).and a11
  refine ⟨0, le_rfl, x0, fun x hx hle ι p hp i hi Y hY s hs1 hs2 => ?_⟩
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨b1, b2⟩, b3⟩, b4⟩, b5⟩, b6⟩, b7⟩, b8⟩, b9⟩, b10⟩, b11⟩ := h x hx hle ι p hp
  clear h a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11
  obtain ⟨-, g1, -, -, -, hfin, -, -⟩ := b1 i hi Y hY
  obtain ⟨hb1, -, -, -, -, hbk, hq⟩ := b2 i
  obtain ⟨⟨u1, hu⟩, hq⟩ := hq hi
  obtain ⟨-, hρ0, hρ1, -⟩ := hq u1 hu
  obtain ⟨δ, hδ, hdg⟩ := b4 i hi Y hY u1 hu
  have hsh := b5 i hi Y hY u1 hu
  obtain ⟨hp1, hq1, hf, hu1, hA, -, hanti⟩ := b6 i hi
  obtain ⟨hL, hj, hL1, -, -, -, -, -, hf8, hr100, -, -, hPP, -, hz1, hz2, -⟩ := b7 i hi Y hY
  have hval := b8 i hi Y hY
  obtain ⟨hC, hl, hF, -⟩ := b9 i hi Y hY
  have hgap := (b10 i hi).gaps
  have hdom := (b11 i).dom
  have hfl := b3 i hi Y hY
  clear b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 hq
  rw [← hu1 u1 hu] at hA hanti hz1 hz2 hval hgap
  clear hu1
  generalize (Fm.parT x hx ι).PP = PP at *
  rw [← CompHS.dimFlag_eq] at hgap
  have hd3 : 3 ≤ CompHt.dimFlag (dat p i) := by
    rw [CompHS.dimFlag_eq, FlagTan.dimFlag]
    exact le_trans hf (Nat.le_mul_of_pos_right _ (Nat.choose_pos (by omega)))
  have hPP100 : 100 ≤ PP := by
    refine le_trans ?_ hPP
    have c1 : (8 : ℝ) ≤ (Fm.D x ι).R.f := by exact_mod_cast hf8
    have c2 : (100 : ℝ) ≤ (Fm.D x ι).R.r := by exact_mod_cast hr100
    have c3 : (8 * 100 * 1 : ℝ) ≤ zBase (Fm.L x ι) := by
      unfold zBase
      gcongr
    exact le_trans (by linarith) (le_self_pow₀ (by linarith) (by norm_num))
  have hT : 1000 * (CompHt.dimFlag (dat p i) : ℝ) ^ 2 ≤ lenT p i PP := by
    refine le_trans ?_ (Nat.le_ceil _)
    have c1 := (Fm.D x ι).R.two_le_m
    have c2 := (Fm.D x ι).R.m_add_three_le_k
    have c3 : (0 : ℝ) < (Fm.D x ι).R.m := by exact_mod_cast (by omega : 0 < (Fm.D x ι).R.m)
    have c4 : ((Fm.D x ι).R.m : ℝ) ≤ (Fm.D x ι).R.k := by exact_mod_cast (by omega : (Fm.D x ι).R.m ≤ (Fm.D x ι).R.k)
    have c5 : 1000 ≤ PP ^ 2 := by nlinarith
    rw [le_div_iff₀ c3]
    gcongr
  obtain ⟨a, ha1, ha2⟩ := exists_jet_order _ _ _ (by omega) hT hρ0 hz2
  have hbir := _root_.GlobalTheory.T.birOn_wtOf_of_consecutive_gap_bound hX hG hQ hSi (_root_.GlobalTheory.T.covering_topology_refinement hP) hP.q15 hP.q16 _ p.T hL _ hp1 hq1 Y _ _ hY.1 u1 fun τ a b hb => by
    rw [← gap_eq _ hb]
    refine le_trans ?_ (hgap τ a (hb ▸ b.2))
    exact_mod_cast bir_gap_le _ _ hd3
  have hboth := GlobalTheory.T.componentImageDegree_between_of_proportionality _ _ _ _ _ _ _ Y.U hY.1.unf (_root_.GlobalTheory.T.proportionality_principle_compactification hP hSi hTo hN _ p.T hL _ hp1 hq1 hf hj Y _ _ hY.1).1
    (_root_.GlobalTheory.T.compactification_top_chern_eq_volume hP hSi hTo hN _ p.T hL _ hp1 hq1 hf hj Y _ _ hY.1) u1 (fun τ => (hA τ).1) (fun τ => (hA τ).2) hbir hval
  have hc0 : 1 ≤ cZero (Fm.D x ι) ((i : ℕ) + 1) := by
    have := (cZeroN_isLeast (Fm.D x ι) ((i : ℕ) + 1)).1.2.2
    unfold cZero
    omega
  have ew : uW p i + (s * cZero (Fm.D x ι) ((i : ℕ) + 1)) • hodgeWt (dat p i) =
      fun τ => uM p i τ + (((s + 1 : ℕ) : ℤ) * cZero (Fm.D x ι) ((i : ℕ) + 1)) • hodgeWt (dat p i) τ := by
    funext τ k
    simp only [uM, uW, uMinus, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    push_cast
    ring
  have em : uW p i + (-(cZero (Fm.D x ι) ((i : ℕ) + 1))) • hodgeWt (dat p i) = uM p i := by
    rw [neg_smul, ← sub_eq_add_neg]
    rfl
  have hl1 : ∀ τ, Antitone ((uW p i + (s * cZero (Fm.D x ι) ((i : ℕ) + 1)) • hodgeWt (dat p i)) τ) := fun τ => by
    rw [ew]
    exact (hanti (s + 1) (by omega) τ).1
  have hl2 : ∀ τ, Antitone (((lenT p i PP + CompHt.dimFlag (dat p i) + 4 : ℕ) : ℤ) • u1 τ -
      (uW p i + (s * cZero (Fm.D x ι) ((i : ℕ) + 1)) • hodgeWt (dat p i)) τ) := fun τ => by
    rw [ew]
    have := (hanti (s + 1) (by omega) τ).2
    rwa [if_neg (Nat.succ_ne_zero s)] at this
  have hl3 : ∀ τ, 1 ≤ gap ((uW p i + (s * cZero (Fm.D x ι) ((i : ℕ) + 1)) • hodgeWt (dat p i)) τ) ((dat p i).p - 1) :=
    fun τ => by
      rw [ew]
      refine le_trans ?_ (le_gap_bar (dat p i) hp1 hq1 (uM p i) τ ?_ _)
      · push_cast
        nlinarith [Int.natCast_nonneg s]
      · simpa using (hanti 0 (by omega) τ).1
  have hev : Even (p.κ i).n := (p.κ i).n_even
  have g2 : Y.GoodAt (Gs p i (s * cZero (Fm.D x ι) ((i : ℕ) + 1))) :=
    _root_.GlobalTheory.CovTop.HodgeSteps.covering_goodAt_shift hP _ p.T hL _ hj Y _ _ hY.1 (le_add_right hp1) hC hl hF _ _ ((Fm.D x ι).R.k - 1) _ hev
      (_root_.GlobalTheory.T.covering_domain_lattice_regularity hP _ p.T hL _ hp1 hq1 hf hj Y _ _ hY.1 _ hl1 hl3).1
  have htw := ((_root_.GlobalTheory.T.twisted_flat_bundle_ranks hP _ p.T hL _ hp1 hq1 hf hj Y _ _ hY.1 _ hfl).2 _ (p.κ i).n ((Fm.D x ι).R.k - 1) · hdom hev)
  rw [htw _ g1, htw _ g2]
  have hk : 0 < PP * kap p i := by linarith
  have hz : zed p i PP u1 ≤ min (1 / 2) ((Fm.L x ι).sc.b / (PP * kap p i)) := le_min hz2 ((le_div_iff₀ hk).2 hz1)
  have hz0 : 0 ≤ zed p i PP u1 := by
    unfold zed
    positivity
  first
    | have hJ := _root_.GlobalTheory.T.jet_rank_complex_le hX hP hSi hTo hG hQ hN
    | have hJ := _root_.GlobalTheory.T.jet_rank_complex_le hP hSi hTo hG hQ hN
  letI := Fintype.ofFinite (Comp Y.d.Xo₂ Y.d.c₂)
  rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, Finset.mul_sum]
  refine Finset.sum_le_sum fun Z _ => ?_
  have d0 : 0 < Y.dg u1 Z := hδ.trans_le (hdg Z).1
  have d1 : (1 - CompHt.rhoB (dat p i) u1) * CompHt.topDeg Y.U Z u1 ≤ Y.dg u1 Z :=
    (CompHt.delPrime_eq Y.U Z (CompHt.vdm_pos fun τ => (hA τ).1).ne').ge.trans (hboth Z Z).1
  have d2 := hJ _ p.T hL _ hp1 hq1 hf hj Y _ _ hY.1 Z u1 _ _ a hgap hl1 hl2 (by
    have h1 : 0 < 1 - CompHt.rhoB (dat p i) u1 := by linarith
    refine lt_of_mul_lt_mul_left ?_ h1.le
    have e1 := mul_le_mul_of_nonneg_left d1 (Nat.cast_nonneg (lenT p i PP + CompHt.dimFlag (dat p i) + 4))
    have e2 := mul_lt_mul_of_pos_right ha1 d0
    linarith)
  calc _ ≤ _ := d2
    _ ≤ (1 + zed p i PP u1) * binT p i PP * Y.dg u1 Z := mul_le_mul_of_nonneg_right ha2 d0.le
    _ ≤ (1 + zed p i PP u1) * Y.rkC (uM p i) Z := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (hsh Z).1 (by linarith)
    _ ≤ _ := by
      rw [← em]
      exact mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg _)
end GlobalTheory.CovTop.HodgeSteps
end
end

section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rk_small_scale_le_of_share : GlobalTheory.CovTop.HypothesesX → _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → GlobalTheory.Published.SiegelToroidalIntegral → GlobalTheory.Published.ToroidalForFanKS → GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.HSCore.Quoted → GlobalTheory.Published.SemiAbelianLieSeminegative → DeepGood → Size → FlatDeg → Deg → Share → Covers fun Fm x _ ι p i Y PP _ => ∀ s : ℕ, 1 ≤ s → s ≤ 2 → (Y.rk (Gs p i (s * cZero (Fm.D x ι) ((i : ℕ) + 1))) : ℝ) ≤ (1 + min (1 / 2) ((Fm.L x ι).sc.b / (PP * kap p i))) * Y.rk (Gs p i (-(cZero (Fm.D x ι) ((i : ℕ) + 1)))) := by
  first | exact @_root_.GlobalTheory.CovTop.HodgeSteps.rk_le_one_add_min_mul_rk_neg | exact _root_.GlobalTheory.CovTop.HodgeSteps.rk_le_one_add_min_mul_rk_neg | (intros; apply _root_.GlobalTheory.CovTop.HodgeSteps.rk_le_one_add_min_mul_rk_neg <;> assumption)
end
