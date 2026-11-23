import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.ExistsSecTieFOfTies
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Formalism.LocalToGlobal.ProjectiveLattices.RecPJThAllNeBot
import Formalism.LocalToGlobal.ProjectiveLattices.PlaceBelow
import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.OEOsInjective
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.RPfVal
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.SpanResCharNeBot
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ConjugateMinimaInstance
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GramSpace
import Formalism.SharpRestriction.Divisibility.WeightAlgebra
import Formalism.LocalToGlobal.ProjectiveLattices.DepRun
import Formalism.LocalToGlobal.ProjectiveLattices.RegXInst
import Formalism.LocalToGlobal.ProjectiveLattices.Adm3OfExtension
import Formalism.LocalToGlobal.ProjectiveLattices.ExistsParameterConditions
import Formalism.LocalToGlobal.ProjectiveLattices.DepthTie
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.TheoremZeroSplitOfLocalAndSum
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.StarRingExtOfStar
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.NumericalConsequencesOfPins
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ThetaGeneratorsLeastValueOverLevelPrimeStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsProductDataCopiesTrivialisationValuation
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.HalfPrincipalAndSplit
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.SplitsInLevelPrime
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.WeightOnDatum
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.EmbEqOfInPsi
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ThetaDepthLeScaledRuleValue
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsShortBasisUniformizationLattice
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsUniformisedModelIntegralChartAtPointStatement

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory NumberField IsLocalRing IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps.EtaleWeightGaps
open GlobalTheory.PtTie

namespace GlobalTheory.DepthOverLevel

theorem lattice_terms_le (R N φ Φ e n n₁ r Dg g c : ℝ) (hR : 0 < R) (hN : 0 < N) (he : 0 < e) (hΦ : 0 ≤ Φ)
    (hΦe : Φ ≤ e * (R * N ^ 3 * φ)) (hn0 : 0 ≤ n₁) (hn : n₁ ≤ n) (hr0 : 0 ≤ r) (hr : r ≤ N) (hD : 1 ≤ Dg) (hg : 0 < g)
    (hc : R * (N ^ 4 * n + 2 * N ^ 3) * Dg ^ 2 / g ≤ c) :
    (n₁ * r * Φ / (4 * g) + 2 * Dg ^ 2 * Φ / g) / e ≤ c * φ := by
  have hφ : 0 ≤ φ := by
    have h1 : 0 ≤ (e * (R * N ^ 3)) * φ := by linarith
    exact nonneg_of_mul_nonneg_right h1 (by positivity)
  have hD2 : 1 ≤ Dg ^ 2 := one_le_pow₀ hD
  have hn' : 0 ≤ n := hn0.trans hn
  have h1 : n₁ * r / 4 ≤ n * N * Dg ^ 2 := by
    have h2 : n₁ * r ≤ n * N := mul_le_mul hn hr hr0 hn'
    have h3 : n * N * 1 ≤ n * N * Dg ^ 2 := mul_le_mul_of_nonneg_left hD2 (by positivity)
    have h4 : 0 ≤ n₁ * r := by positivity
    linarith
  calc (n₁ * r * Φ / (4 * g) + 2 * Dg ^ 2 * Φ / g) / e = (n₁ * r / 4 + 2 * Dg ^ 2) * Φ / g / e := by
        field_simp
    _ ≤ (n * N * Dg ^ 2 + 2 * Dg ^ 2) * (e * (R * N ^ 3 * φ)) / g / e := by gcongr
    _ = R * (N ^ 4 * n + 2 * N ^ 3) * Dg ^ 2 / g * φ := by field_simp
    _ ≤ c * φ := by gcongr

theorem not_isUnit_of_vV_ne_zero (S : CDVR) (N : ℕ) (h : vV S.V ((N : ℕ) : S.Fr) ≠ 0) : ¬ IsUnit ((N : ℕ) : S.V) := by
  intro hu
  apply h
  have h2 : valV S.V (algebraMap S.V S.Fr ((N : ℕ) : S.V)) = 1 := by
    unfold valV
    rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff]
    exact fun h => (mem_nonunits_iff.1 h) hu
  rw [map_natCast] at h2
  unfold vV
  rw [h2]
  simp

theorem vLa_sWt {D : D7} {j : ℕ} (B : WeightFamilies.Prov D) (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D)
    (w : WeightFamilies.Wt D j) (la : HeightOneSpectrum (𝓞 B.KO)) (i : Fin 2) (hg : ((D.host.g i : ℕ) : 𝓞 B.KO) ∈ la.asIdeal) :
    sWt B hinj EX w ≠ 0 ∧ ((nnW B hinj EX w : 𝓞 B.KO) : B.KO) ≠ 0 ∧
      vLa la ((sWt B hinj EX w : 𝓞 B.KO) : B.KO) = vLa la ((nnW B hinj EX w : 𝓞 B.KO) : B.KO) := by
  have hq : D.host.q.Prime := D.host.hyp.1
  have hd : D.host.d.Prime := D.host.hyp.2.1
  have hq8 : D.host.q % 8 = 3 := D.host.hyp.2.2.1
  have hd16 : D.host.d % 16 = 7 := D.host.hyp.2.2.2.1
  have hnd : ¬ D.host.g i ∣ D.host.condN := fun h => by
    have hc : D.host.g i % D.host.condN = 1 := D.ntypes.g_cond i
    have h1 := Nat.mod_mod_of_dvd (D.host.g i) h
    rw [hc, Nat.mod_self, Nat.mod_eq_of_lt (D.host.g_prime i).one_lt] at h1
    exact one_ne_zero h1
  have hl : resCharOf la = D.host.g i := (RPfVal.prime_mem_iff la (D.host.g_prime i)).1 hg
  have hnn : nnW B hinj EX w ≠ 0 := by
    have hπ : ∀ k, iE D hinj B (EX.piG k) ≠ 0 ∧ iE D hinj B (piBarO EX k) ≠ 0 := by
      intro k
      rw [← mul_ne_zero_iff, ← map_mul, RPfVal.piG_mul_bar, map_natCast]
      exact Nat.cast_ne_zero.2 (D.host.g_prime k).ne_zero
    exact Finset.prod_ne_zero_iff.2 fun k _ => mul_ne_zero (pow_ne_zero _ (hπ k).1) (pow_ne_zero _ (hπ k).2)
  have hnn0 : ((nnW B hinj EX w : 𝓞 B.KO) : B.KO) ≠ 0 := fun h =>
    hnn (NumberField.RingOfIntegers.coe_eq_zero_iff.1 h)
  have hP : pPow D (c2 D w) (cHalf w) (cHalf w) = D.host.QS ^ c2 D w * D.host.q ^ cHalf w * D.host.d ^ cHalf w := rfl
  have hN : pPow D (c2 D w) (cHalf w) (cHalf w) ≠ 0 :=
    Nat.mul_ne_zero (Nat.mul_ne_zero (pow_ne_zero _ D.host.QS_pos.ne') (pow_ne_zero _ hq.ne_zero))
      (pow_ne_zero _ hd.ne_zero)
  refine ⟨mul_ne_zero hnn (Nat.cast_ne_zero.2 hN), hnn0, ?_⟩
  have hc : ((sWt B hinj EX w : 𝓞 B.KO) : B.KO) =
      ((nnW B hinj EX w : 𝓞 B.KO) : B.KO) * ((pPow D (c2 D w) (cHalf w) (cHalf w) : ℕ) : B.KO) := by
    show algebraMap (𝓞 B.KO) B.KO (_ * _) = _
    rw [map_mul, map_natCast]
  rw [hc, Crude.crv_vLa_mul la hnn0 (Nat.cast_ne_zero.2 hN), hP, RPfVal.vLa_pPow la D.host.QS_pos.ne' hq hd, hl,
    padicValNat.eq_zero_of_not_dvd (fun h => hnd (h.trans D.host.QS_dvd_condN)),
    if_neg (D.host.ne_q_of_not_dvd hnd), if_neg (D.host.ne_d_of_not_dvd hnd)]
  simp

theorem nusOf_of_mem {D : D7} {j : ℕ} (B : WeightFamilies.Prov D) (w : WeightFamilies.Wt D j) (nu : HeightOneSpectrum (𝓞 B.KO) → ℝ)
    (la : HeightOneSpectrum (𝓞 B.KO)) (i : Fin 2) (hg : ((D.host.g i : ℕ) : 𝓞 B.KO) ∈ la.asIdeal) :
    nusOf B w nu la = (ramOverZ la : ℝ) * (WeightAlgebra.DF w : ℝ) / ((D.host.g i : ℝ) - 1) := by
  have h : ∃ i : Fin 2, ((D.host.g i : ℕ) : 𝓞 B.KO) ∈ la.asIdeal := ⟨i, hg⟩
  have h1 : D.host.g (Classical.choose h) = D.host.g i :=
    ((RPfVal.prime_mem_iff la (D.host.g_prime _)).1 (Classical.choose_spec h)).symm.trans
      ((RPfVal.prime_mem_iff la (D.host.g_prime i)).1 hg)
  unfold nusOf
  rw [dif_pos h, h1, H1algLink.eWL_eq]

theorem wtA_antitone {D : D7} {j : ℕ} (w : WeightFamilies.Wt D j) (τ : D.host.E →+* ℂ) : Antitone fun i => wtA w (τ, i) := by
  intro i i' hii
  unfold wtA
  refine Finset.sum_le_sum fun t _ => add_le_add ?_ ?_
  · split_ifs
    · exact partitionExtendByZero_antitone (w.aPlus_antitone t) hii
    · exact le_rfl
  · split_ifs
    · exact partitionExtendByZero_antitone (w.aM_anti t) hii
    · exact le_rfl

theorem depth_le_over_level : (∀ (p : ℕ) [Fact p.Prime], Pdiv.ChartF.HTFSt p) → ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D) (w : WeightFamilies.Wt D j) (c : ℝ), Oriented T EX → RunNum D w c → ∀ (la : HeightOneSpectrum (𝓞 T.Q.c.F)) (i : Fin 2), ((D.host.g i : ℕ) : 𝓞 T.Q.c.F) ∈ la.asIdeal → ∀ y : T.PtA j la, (recPJ h j hj).depth (sWt (recB h.toLawsCore) hinj EX w) w la y ≤ ((nusOf (recB h.toLawsCore) w (nuWt T w) la + c * (recPJ h j hj).phiC la y : ℝ) : EReal) := by
  intro hHT D T h j hj hinj EX w c hO hR la i hg y
  letI := T.Q.H.starRing
  obtain ⟨hlast, hn, hDg, hc0, hc⟩ := hR
  obtain ⟨S, io, e, ho, z, hz, hl, C, Pu, hC, hPu, hval⟩ := GlobalTheory.T.exists_uniformisedModel_integralChart_at_point D T h j hj la y
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible S.V
  obtain ⟨⟨Q, hQ⟩, -⟩ := GlobalTheory.PowData.exists_powData _ T.Q.H (T.Q.Dw j) T.Q.l (T.Q.Xo j) T.Q.c S io z C Pu ϖ hϖ
  obtain ⟨r, Φ, M0, ⟨hΦ, b, hb1, hb2⟩, hr, hM0, hjm, hΦe⟩ :=
    GlobalTheory.ShortBasisAt.exists_shortBasis D T h j hj la S io e ho z hz (imgV y) hl C Pu ϖ hϖ Q hQ
  have hphi : (recPJ h j hj).phiC la (PtV.mk la ho z hz (imgV y) hl) = (recPJ h j hj).phiC la y := rfl
  rw [hphi] at hΦe
  have hM := h.toLawsCore.toLawsM
  obtain ⟨hDF, -, hpos, -, -, hf1, hr1, hrank⟩ := GlobalTheory.WeightOnDatum.weight_on_datum D T.toCore hM.pins j hj w
  have hD1 := (hpos hlast).2
  have hpq := ((GlobalTheory.PinNum.numerics_of_pins D T.Q hM.pins).2.2.2.2.2.2 j hj).1
  obtain ⟨-, hst, hMb, -⟩ := GlobalTheory.HalfGen.half_principal_and_split D T.toCore hM EX
  have hMb := hMb hO
  have hnab : IsNab (T.Q.Xo j) T.Q.c (T.nab j) := by
    obtain ⟨st, hn⟩ := h.nabPin j hj
    have := GlobalTheory.PowGerm.starSt _ T.Q.H st hn.1
    subst this
    exact hn
  obtain ⟨i', hne, hMg, hMb', hα⟩ : ∃ i' : Fin 2, D.host.g i ≠ D.host.g i' ∧ T.Q.l.M = D.host.g i' * D.host.g i ∧
      T.Q.l.Mb = Ideal.span {piBarO EX i * piBarO EX i'} ∧
      star (piBarO EX i) * star (piBarO EX i') = EX.piG 0 * EX.piG 1 := by
    have hs : ∀ k, star (piBarO EX k) = EX.piG k := fun k => by rw [← (hst k).1, star_star]
    have hLM := level_M T.toCore hM
    fin_cases i
    · exact ⟨1, D.host.g_ne, hLM.trans (mul_comm _ _), hMb, by rw [hs, hs]; rfl⟩
    · exact ⟨0, D.host.g_ne.symm, hLM, by rw [hMb, mul_comm]; rfl, by rw [hs, hs, mul_comm]; rfl⟩
  have hres : resCharOf la = D.host.g i := (RPfVal.prime_mem_iff la (D.host.g_prime i)).1 hg
  have hvg : vV S.V ((D.host.g i : ℕ) : S.Fr) = (e : ℤ) * ramOverZ la := by
    rw [← map_natCast io, ho.2, ← hres, Crude.crv_vLa_char]
  have hnu : ¬ IsUnit ((D.host.g i : ℕ) : S.V) := by
    refine not_isUnit_of_vV_ne_zero S _ ?_
    rw [hvg]
    exact mul_ne_zero (Nat.cast_ne_zero.2 ho.1.ne') (Nat.cast_ne_zero.2 (H1algLink.ramOverZ_ne_zero la))
  have hsp := GlobalTheory.LevelSplit.splitsIn_level_prime D i
  have hg' : (0 : ℝ) < D.host.g i' := by exact_mod_cast (D.host.g_prime i').pos
  have he : (0 : ℝ) < e := by exact_mod_cast ho.1
  have hnr : 2 * D.R.r ≤ w.n := le_trans (by nlinarith) hn
  have hDM : (WeightAlgebra.DF w : ℝ) * M0 < D.host.g i' := by
    by_cases hlt : j < D.R.m
    · exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left hM0 (Nat.cast_nonneg _)) (hc hlt i').1
    · rw [(hjm (not_lt.1 hlt)).1, mul_zero]; exact hg'
  have hA := GlobalTheory.T.theta_generators_least_value_over_level_prime hHT _ T.Q.H (T.Q.Dw j) T.Q.l (T.Q.Xo j) T.Q.c (T.nab j) hnab (h.thTot j hj) S io z C hC
    Pu hPu hz ϖ hϖ Q hQ Φ M0 r b hΦ hb1 hb2 (D.host.g i) (D.host.g i') (D.host.g_prime i) (D.host.g_prime i') hne hMg
    (piBarO EX i) (piBarO EX i') (hst i).2 (hst i').2 hMb' hsp.1 hsp.2 hnu (wtA w) w.n e
    (wtA_antitone w) (by rw [hpq]; exact hnr) (by omega) ho.1
    (by rw [hDF]; have := hDg i; omega) (by rw [hDF]; exact hDg i') (by rw [hDF]; exact hDM)
  obtain ⟨hs0, hnn0, hsv⟩ := vLa_sWt (recB h.toLawsCore) hinj EX w la i hg
  have hN : nval S.V e (∏ τ : D.host.E →+* ℂ, (io (embK T.Q.c τ (star (piBarO EX i) * star (piBarO EX i')))) ^
      (∑ k : Fin ((T.Q.Dw j).mult τ), wtA w (τ, k))) =
      (((vLa la ((sWt (recB h.toLawsCore) hinj EX w : 𝓞 T.Q.c.F) : T.Q.c.F) : ℤ) : ℝ) : EReal) := by
    have h1 : (∏ τ : D.host.E →+* ℂ, (io (embK T.Q.c τ (star (piBarO EX i) * star (piBarO EX i')))) ^
        (∑ k : Fin ((T.Q.Dw j).mult τ), wtA w (τ, k))) =
        io ((nnW (recB h.toLawsCore) hinj EX w : 𝓞 T.Q.c.F) : T.Q.c.F) := by
      rw [← GlobalTheory.PtTie.nrm_eq_nnW D T h j hj hinj EX w, hα]
      unfold nrm
      simp only [map_prod, map_pow]
    rw [h1, nval_of_ne ((map_ne_zero io).2 hnn0), ho.2]
    refine congrArg (fun x : ℝ => (x : EReal)) ?_
    rw [Int.cast_mul, Int.cast_natCast, mul_div_cancel_left₀ _ he.ne']
    exact congrArg (fun x : ℤ => (x : ℝ)) hsv.symm
  rw [hN, hDF, hpq, hvg] at hA
  have hdep : (recPJ h j hj).depth (sWt (recB h.toLawsCore) hinj EX w) w la y ≤
      (⨅ f ∈ T.th j w, nval S.V e (evI z f)) +
        (((vLa la ((sWt (recB h.toLawsCore) hinj EX w : 𝓞 T.Q.c.F) : T.Q.c.F) : ℤ) : ℝ) : EReal) := by
    rw [← EReal.sub_le_iff_le_add (Or.inl (EReal.coe_ne_bot _)) (Or.inl (EReal.coe_ne_top _))]
    refine le_iInf₂ fun f hf => ?_
    rw [EReal.sub_le_iff_le_add (Or.inl (EReal.coe_ne_bot _)) (Or.inl (EReal.coe_ne_top _)), ← hval w f hf, add_comm]
    exact GlobalTheory.DepthRule.depth_le_scaled_value D T h j hj w hlast _ hs0 la y f hf
  refine hdep.trans (le_trans hA (EReal.coe_le_coe_iff.2 ?_))
  rw [nusOf_of_mem (recB h.toLawsCore) w _ la i hg, add_assoc, add_div]
  refine add_le_add (le_of_eq ?_) ?_
  · push_cast
    rw [mul_assoc, mul_div_assoc, mul_div_cancel_left₀ _ he.ne']
  · by_cases hlt : j < D.R.m
    · have hm := D.R.two_le_m
      have hf' : (0 : ℝ) < D.R.f := by exact_mod_cast hf1
      have hm' : (0 : ℝ) < D.R.m := by exact_mod_cast (by omega : 0 < D.R.m)
      refine lattice_terms_le (rr0 D) (2 * D.R.f * D.R.m) _ Φ e w.n _ r _ _ c ?_ (by positivity) he hΦ hΦe
        (Nat.cast_nonneg _) (by exact_mod_cast (by omega : D.R.r ≤ w.n)) (Nat.cast_nonneg _) (by exact_mod_cast hr)
        (by exact_mod_cast hD1) hg' (hc hlt i').2
      unfold rr0
      have hd : (0 : ℝ) < |(NumberField.discr D.host.E : ℝ)| :=
        abs_pos.2 (Int.cast_ne_zero.2 (NumberField.discr_ne_zero _))
      have hk : (0 : ℝ) < Module.finrank ℚ D.host.E := by exact_mod_cast Module.finrank_pos
      positivity
    · have h0 : (recPJ h j hj).phiC la y = 0 := by
        unfold WeightAlgebra.PJ.phiC
        rw [if_neg hlt]
      rw [h0, (hjm (not_lt.1 hlt)).2]
      simp

end GlobalTheory.DepthOverLevel
