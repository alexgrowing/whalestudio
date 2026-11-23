import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.WinUpDown
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.PrincipalSeriesMatching.PolFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.PrincipalSeriesMatching.GamLocX
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.GammaLaurentFactors.LocalEmbeddingNorms.LocIso
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ArchimedeanSchwartz.ArchimedeanDerivatives.ExpAlg
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ArchimedeanSchwartz.ArchimedeanDerivatives.ExpIndep
import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ArchimedeanSchwartz.ArchimedeanDerivatives.LocUnr
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ArchimedeanSchwartz.ArchimedeanDerivatives.SatDict
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ArchimedeanSchwartz.ArchimedeanDerivatives.CoefSm
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ArchimedeanSchwartz.ArchimedeanDerivatives.SideCenOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ArchimedeanSchwartz.ArchimedeanDerivatives.SideOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ArchimedeanSchwartz.ArchimedeanDerivatives.ExistsPullback
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ArchimedeanSchwartz.ArchimedeanDerivatives.Regroup
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ArchimedeanSchwartz.ArchimedeanDerivatives.UnionOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ArchimedeanSchwartz.ArchimedeanDerivatives.CharSep
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnramifiedAtValueHeckeCharCompIdeleNorm
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsGoodConjSelfDualTwistSplitUnramifiedStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeLAdicCharacterAndPrincipalIdealSt
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeilDeligneParamOfLadicRepTwistDetAwayFromL
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.QuadraticTwists.AttTwist
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ArchimedeanSchwartz.ArchimedeanDerivatives.EventuallyUnr
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ArchimedeanSchwartz.ArchimedeanDerivatives.ContDiffFderivApply
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ArchimedeanSchwartz.ArchimedeanDerivatives.HasDerivAtProdLog
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ArchimedeanSchwartz.ArchimedeanDerivatives.ShiftOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ArchimedeanSchwartz.ArchimedeanDerivatives.HasFDerivAtExpF
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ArchimedeanSchwartz.ArchimedeanDerivatives.TestEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ArchimedeanSchwartz.ArchimedeanDerivatives.IsOpenEmbeddingVal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ArchimedeanSchwartz.ArchimedeanDerivatives.BridgeOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ArchimedeanSchwartz.ArchimedeanDerivatives.ArchOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ArchimedeanSchwartz.GenericFunctionalEquation.GenFE
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHasInfCharGL
import GroundTheory.AutomorphicForms.GL2.GJLocalFEGamma
import GroundTheory.GlobalFields.TateThesis.RootNumberLocalPlace

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Polynomial Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.HenQ Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.GJStandardL GroundTheory.Automorphic.GodementJacquet
open GroundTheory.Automorphic.GLnLocal GroundTheory.Automorphic.GJStandardLCuspidal UpperTheory.V UpperTheory.V.Z.Inf UpperTheory.V.Z.Gam UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter

attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL

private theorem eval_quot (N D : ℂ[X]) (x : ℂ) (hD : D.eval x ≠ 0) :
    (algebraMap ℂ[X] (RatFunc ℂ) N / algebraMap ℂ[X] (RatFunc ℂ) D).eval (RingHom.id ℂ) x = N.eval x / D.eval x := by
  have hD0 : D ≠ 0 := fun e => hD (by simp [e])
  set R := algebraMap ℂ[X] (RatFunc ℂ) N / algebraMap ℂ[X] (RatFunc ℂ) D with hR
  have h1 : R.denom ∣ D := RatFunc.denom_div_dvd N D
  have h2 : R.denom.eval x ≠ 0 := fun e => by
    obtain ⟨u, hu⟩ := h1
    exact hD (by rw [hu, eval_mul, e, zero_mul])
  have h3 : R.num * D = N * R.denom := (RatFunc.num_mul_eq_mul_denom_iff hD0).2 hR
  have h4 := congrArg (eval x) h3
  simp only [eval_mul] at h4
  simp only [RatFunc.eval, eval₂_id]
  rw [div_eq_div_iff h2 hD, h4]

private theorem loc_dual {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (P : ℂ[X]) (c Q b : ℂ) (j : ℤ) (hP : P.eval 0 = 1) {A B : ℂ → ℂ}
    (h : RatFE F (RatFunc.C c * RatFunc.X ^ j * algebraMap ℂ[X] (RatFunc ℂ) P /
      algebraMap ℂ[X] (RatFunc ℂ) (P.comp (C Q * X))) A B) (hA : ∀ s, A s = b) :
    ∃ r : ℝ, ∀ s : ℂ, s.re < -r → B s = c * b * qs F s ^ j * P.eval (qs F s) / P.eval (Q * qs F s) := by
  obtain ⟨R, s₁, h1, h2⟩ := h
  have hR : R = RatFunc.C b := eq_of_eval_qs_eq_right (F := F) (s₁ := s₁) fun s hs => by
    rw [← h1 s hs, hA, RatFunc.eval_C]
    rfl
  have hD0 : P.comp (C Q * X) ≠ 0 := fun e => by
    have := congrArg (eval 0) e
    simp [eval_comp, hP] at this
  obtain ⟨Bd, hB, h4⟩ := exists_norm_gt_eval_ne_zero hD0
  have hq : (1 : ℝ) < GroundTheory.LocalField.residueCard F := by exact_mod_cast GroundTheory.LocalField.one_lt_residueCard
  refine ⟨max s₁ (Real.logb (GroundTheory.LocalField.residueCard F) Bd), fun s hs => ?_⟩
  have hs1 := le_max_left s₁ (Real.logb (GroundTheory.LocalField.residueCard F) Bd)
  have hs2 := le_max_right s₁ (Real.logb (GroundTheory.LocalField.residueCard F) Bd)
  have h5 : (P.comp (C Q * X)).eval (qs F s) ≠ 0 := h4 _ (by
    rw [norm_qs]
    calc Bd = (GroundTheory.LocalField.residueCard F : ℝ) ^ (Real.logb (GroundTheory.LocalField.residueCard F) Bd) :=
          (Real.rpow_logb (by linarith) hq.ne' hB).symm
      _ < _ := Real.rpow_lt_rpow_of_exponent_lt hq (by linarith))
  have hx : qs F s ≠ 0 := qs_ne_zero s
  have hj : j = (j.toNat : ℤ) - ((-j).toNat : ℤ) := (Int.toNat_sub_toNat_neg j).symm
  have e : RatFunc.C c * RatFunc.X ^ j * algebraMap ℂ[X] (RatFunc ℂ) P /
      algebraMap ℂ[X] (RatFunc ℂ) (P.comp (C Q * X)) * RatFunc.C b =
      algebraMap ℂ[X] (RatFunc ℂ) (C c * C b * X ^ j.toNat * P) /
        algebraMap ℂ[X] (RatFunc ℂ) (X ^ (-j).toNat * P.comp (C Q * X)) := by
    simp only [map_mul, map_pow, RatFunc.algebraMap_C, RatFunc.algebraMap_X]
    rw [hj, zpow_sub₀ RatFunc.X_ne_zero, zpow_natCast, zpow_natCast, ← hj]
    ring
  rw [h2 s (by linarith), hR, e, eval_quot _ _ _ (by rw [eval_mul, eval_pow, eval_X]; exact mul_ne_zero (pow_ne_zero _ hx) h5)]
  simp only [eval_mul, eval_pow, eval_X, eval_C, eval_comp]
  rw [hj, zpow_sub₀ hx, zpow_natCast, zpow_natCast, ← hj]
  ring

private theorem comb {I : Type} (S : Finset I) (N : I → ℕ) (P : I → ℂ[X]) (c : I → ℂ) (j : I → ℤ) (q : ℕ) (f d : I → ℕ)
    (hq : 1 < q) (h : ∀ v ∈ S, 1 < N v ∧ (P v).eval 0 = 1 ∧ (P v).natDegree = d v ∧ (d v ≠ 0 → N v = q ^ f v)) :
    ∃ (c₀ : ℂ) (t : ℝ), ∀ s : ℂ,
      ∏ v ∈ S, c v * ((N v : ℂ) ^ (-s)) ^ j v * (P v).eval ((N v : ℂ) ^ (-s)) / (P v).eval (N v * (N v : ℂ) ^ (-s)) =
        fac c₀ t q (∏ v ∈ S, (P v).comp (X ^ f v)) s := by
  have h1 : ∀ v ∈ S, d v = 0 → P v = 1 := fun v hv e => by
    have a := eq_C_of_natDegree_eq_zero ((h v hv).2.2.1.trans e)
    have b := (h v hv).2.1
    rw [a, eval_C] at b
    rw [a, b, C_1]
  have hev : ∀ v ∈ S, ∀ u : ℂ, ((P v).comp (X ^ f v)).eval (((q : ℝ) : ℂ) ^ u) = (P v).eval ((N v : ℂ) ^ u) := fun v hv u => by
    by_cases e : d v = 0
    · simp [h1 v hv e]
    · rw [eval_comp, eval_pow, eval_X, (h v hv).2.2.2 e, Nat.cast_pow, ← Complex.natCast_cpow_natCast_mul,
        Complex.ofReal_natCast, Complex.cpow_nat_mul]
  refine ⟨∏ v ∈ S, c v, ∑ v ∈ S, -(j v * Real.log (N v)), fun s => ?_⟩
  · rw [fac, eval_prod, eval_prod, Complex.ofReal_sum, Finset.sum_mul, Complex.exp_sum, ← Finset.prod_mul_distrib,
      ← Finset.prod_mul_distrib, ← Finset.prod_div_distrib]
    refine Finset.prod_congr rfl fun v hv => ?_
    have hN : (N v : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by have := (h v hv).1; omega)
    rw [hev v hv, hev v hv, sub_eq_add_neg, Complex.cpow_add _ _ hN, Complex.cpow_one]
    congr 3
    rw [Complex.cpow_def_of_ne_zero hN, ← Complex.exp_int_mul, ← Complex.natCast_log]
    congr 1
    push_cast
    ring

private theorem far_ne {A : ℂ → ℂ} (hA : Differentiable ℂ A) (h0 : A ≠ 0) (c : ℝ) : ∃ s : ℂ, c < s.re ∧ A s ≠ 0 := by
  by_contra h
  push Not at h
  refine h0 (funext fun x => AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero
    (hA.differentiableOn.analyticOnNhd isOpen_univ) isPreconnected_univ (Set.mem_univ ((c + 1 : ℝ) : ℂ)) ?_ trivial)
  filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
    (show c < ((c + 1 : ℝ) : ℂ).re by simp)] with s hs using h s hs

set_option maxHeartbeats 1600000 in
theorem UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.sideXCen :
    UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.SideXCen := by
  have hGL := gamLocX
  have hLI := locIso
  intro K _ _ _ n hn σ h S hRS B hB sp q f hq hsp
  classical
  have hLU := locUnr
  have hSD := satDict
  have hCS := coefSm
  have hAS := archOf (shiftOf (ptwOf weyl) parts) fourD testEx (bridgeOf haarL)
  choose m hm using fun τ : K →+* ℂ => (GlobalTheory.ResW.IrrInfChar.main K n τ).1 σ
  have hn1 : 1 ≤ n := by omega
  obtain ⟨D⟩ := (Cm.toRep σ h).nonempty_adelicDecomposition
  let μ : Measure (Reduction.normOneGL K n) := Measure.haar
  obtain ⟨a, x, hx, ha, hx0, hxK⟩ := exists_pureTensor_spherical _ D
  obtain ⟨ℓ, fi, hℓs, hℓ1, hℓK, hf, hF1⟩ := matrixCoeff_factorization_of_pureTensor _ D μ a x hx ha hx0
  have hfix : ∀ v ∉ S, x v ∈ fixedVectors (D.finite.π v) (integralGL (v.adicCompletion K) n) := fun v hv =>
    hxK v ((hLI K n σ h D v).2 _ (hB v hv))
  have hsm : ∀ v, x v ∈ smoothVectors (D.finite.π v) := fun v => (D.finite.isAdmissible v).1 (x v)
  set φ₀ : cuspForms K n := Phi0 _ D a x hx with hφ₀
  have hmem : φ₀ ∈ Cm.carrier σ := (phi D a x hx).2
  have hf' : ∀ g, GJGlobal.matrixCoeff μ φ₀.1 φ₀.1 g = fi (archComp K n g) *
      ∏ᶠ v : HeightOneSpectrum (𝓞 K), Parabolic.matrixCoeff (F := v.adicCompletion K) (D.finite.π v) (x v) (ℓ v)
        (localComp n v g) := hf
  have hF1' : GJGlobal.matrixCoeff μ φ₀.1 φ₀.1 1 ≠ 0 := hF1
  have hone : ∀ v : HeightOneSpectrum (𝓞 K),
      Parabolic.matrixCoeff (F := v.adicCompletion K) (D.finite.π v) (x v) (ℓ v) 1 = 1 := fun v => by
    simpa [Parabolic.matrixCoeff] using hℓ1 v

  obtain ⟨T, hT, hTc⟩ := hCS K n hn1 μ σ h φ₀
  let p : σ.V := ⟨Cm.ofCusp K n φ₀, hmem⟩
  have hfi : ∀ y, fi y = (T p).1 ((AdelicGLn.prodEquiv K n).symm (y, 1)) := fun y => by
    have e1 : archComp K n ((AdelicGLn.prodEquiv K n).symm (y, 1)) = y :=
      congrArg Prod.fst ((AdelicGLn.prodEquiv K n).apply_symm_apply (y, 1))
    have e2 : ∀ v, localComp n v ((AdelicGLn.prodEquiv K n).symm (y, 1)) = 1 := fun v => by
      have e : finComp K n ((AdelicGLn.prodEquiv K n).symm (y, 1)) = 1 :=
        congrArg Prod.snd ((AdelicGLn.prodEquiv K n).apply_symm_apply (y, 1))
      change AdelicGLn.finiteRestrictedEquiv K n (finComp K n _) v = 1
      rw [e, map_one, RestrictedProduct.one_apply]
    rw [hT]
    change _ = GJGlobal.matrixCoeff μ φ₀.1 φ₀.1 _
    rw [hf', e1]
    simp [e2, hone]
  have hfi0 : ∃ y, fi y ≠ 0 := ⟨_, left_ne_zero_of_mul (hf' 1 ▸ hF1')⟩
  obtain ⟨φ, φ', k, k', hk, hk', hAd, hA0, hsh, hsh'⟩ := hAS K n hn1 (T p) m (fun τ u => by
    rw [← hTc τ u p (((m τ).map (u + ·)).prod • p) (show _ = _ by first | exact (hm τ u _ hmem).symm | exact ((hm τ).2 u _ hmem).symm | exact (hm τ _ hmem u).symm | exact ((hm τ).2 _ hmem u).symm), map_smul]) fi hfi hfi0 Measure.haar

  have hz : ∀ v, ∃ z : Fin n → ℂˣ, v ∉ S →
      Spherical.IsSatakeParameter (F := v.adicCompletion K) (D.finite.π v) (localHaar n v) z ∧ B v = Finset.univ.val.map z :=
    fun v => by
      by_cases hv : v ∈ S
      · exact ⟨1, fun e => absurd hv e⟩
      · exact (hSD K n σ h D v _ (hB v hv)).imp fun z hz _ => hz
  choose z hz using hz
  have hb := fun v : HeightOneSpectrum (𝓞 K) => exists_localBump (localHaar n v) (D.finite.π v) (hsm v) (ℓ v) (g₀ := 1)
    (by rw [hone]; exact one_ne_zero)
  choose Φb hΦb b hb0 hb using hb
  let Φ : ∀ v : HeightOneSpectrum (𝓞 K), Matrix (Fin n) (Fin n) (v.adicCompletion K) → ℂ :=
    fun v => if v ∈ S then Φb v else integralIndicator (v.adicCompletion K) n
  have hΦS : ∀ v ∈ S, Φ v = Φb v := fun v hv => if_pos hv
  obtain ⟨c, c', hc, hc', hSB1, hG⟩ := genFE hn μ φ₀.2 φ₀.2 (h hmem) S hRS
    D.finite.π x ℓ hsm hℓs (fun v hv => ⟨hfix v hv, hℓ1 v⟩) (fun v hv => hℓK v (hfix v hv)) D.finite.isIrreducible
    D.finite.isAdmissible z (fun v hv => (hz v hv).1) fi hf' ⟨1, hF1'⟩ Φ (fun v hv => hΦS v hv ▸ hΦb v)
    (fun v hv => if_neg hv)
  obtain ⟨σ₁, Λ, hΛ, h1⟩ := hG φ
  obtain ⟨σ₂, Λ', hΛ', h2⟩ := hG φ'
  have hloc : ∀ s, ∏ v ∈ S, zetaIntegral (localHaar n v) (Φ v)
      (Parabolic.matrixCoeff (F := v.adicCompletion K) (D.finite.π v) (x v) (ℓ v)) s = ∏ v ∈ S, b v := fun s =>
    Finset.prod_congr rfl fun v hv => by rw [hΦS v hv, (hb v s).2.2, detPow, GodementJacquet.absDet]; simp
  have hU := fun v (hv : v ∉ S) => hLU K n hn1 v _ (D.finite.π v) (D.finite.isIrreducible v) (D.finite.isAdmissible v)
    (fun e => hx0 v (by simpa [e] using hfix v hv)) (z v) (hz v hv).1
  have hL : ∀ s, partialL S D.finite.π s = eulerL K (cx B) S s := fun s =>
    tprod_congr fun v => by
      rw [(hU v.1 v.2 s).1, cx, (hz v.1 v.2).2, Multiset.map_map, Multiset.map_map]
      rfl
  have hL' : ∀ s, dualPartialL S D.finite.π (1 - s) = eulerLd K (cx B) S s := fun s =>
    tprod_congr fun v => by
      rw [(hU v.1 v.2 (1 - s)).2]
      simp only [cx]
      rw [(hz v.1 v.2).2, Multiset.map_map, Multiset.map_map, Multiset.map_map]
      rfl
  have hd : ∀ v, ∃ (P : ℂ[X]) (e : ℂ) (j : ℤ) (c : ℝ), v ∈ S → P = pol (sp v) 1 ∧ P.eval 0 = 1 ∧ P.natDegree = cnt (sp v) 1 ∧
      ∀ s : ℂ, s.re < -c →
      zetaIntegral (localHaar n v) (GJMatrix.localMatrixFourier (GroundTheory.Global.localAdelicChar K v) (Φ v))
        (fun g => Parabolic.matrixCoeff (F := v.adicCompletion K) (D.finite.π v) (x v) (ℓ v) g⁻¹) (1 - s) =
        e * (((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s)) ^ j * P.eval (((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s)) /
          P.eval (((Ideal.absNorm v.asIdeal : ℕ) : ℂ) * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s)) :=
    fun v => by
      by_cases hv : v ∈ S
      · obtain ⟨e, j, -, hγ⟩ := hGL K n hn1 v _ (D.finite.π v) (sp v) ((hLI K n σ h D v).1 _ (hsp v hv).1)
        obtain ⟨hP0, hPd, -⟩ := (polFacts (v.adicCompletion K)).2.2.2 (sp v) 1
        obtain ⟨r, hr⟩ := loc_dual (pol (sp v) 1) e _ (b v) j hP0 (hγ (Φ v) (hΦS v hv ▸ hΦb v) (x v) (ℓ v) (hℓs v)) fun s => by
          rw [hΦS v hv, (hb v s).2.2, detPow, GodementJacquet.absDet]; simp
        refine ⟨pol (sp v) 1, e * b v, j, r, fun _ => ⟨rfl, hP0, hPd, fun s hs => ?_⟩⟩
        have hqs : qs (v.adicCompletion K) s = ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s) := by
          rw [qs, GroundTheory.Global.residueCard_adicCompletion]
        rw [← hqs]
        exact hr s hs
      · exact ⟨0, 0, 0, 0, fun e => absurd e hv⟩
  choose P e j cv hd using hd
  obtain ⟨c₀, t, hfac⟩ := comb S (fun v => Ideal.absNorm v.asIdeal) P e j q f (fun v => cnt (sp v) 1) hq
    fun v hv => ⟨NumberField.HeightOneSpectrum.one_lt_absNorm v, (hd v hv).2.1, (hd v hv).2.2.1, (hsp v hv).2⟩
  have hPe : ∏ v ∈ S, (pol (sp v) 1).comp (X ^ f v) = ∏ v ∈ S, (P v).comp (X ^ f v) :=
    Finset.prod_congr rfl fun v hv => by rw [(hd v hv).1]
  rw [hPe]
  generalize ∏ v ∈ S, (P v).comp (X ^ f v) = P₀ at hfac ⊢
  have hb' : ∏ v ∈ S, b v ≠ 0 := Finset.prod_ne_zero_iff.2 fun v _ => hb0 v
  set r : ℝ := |σ₁| + |σ₂| + ∑ v ∈ S, |cv v| + 2 with hr
  have hs0 : 0 ≤ ∑ v ∈ S, |cv v| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have a1 := le_abs_self σ₁
  have a2 := le_abs_self σ₂
  have a3 := abs_nonneg σ₁
  have a4 := abs_nonneg σ₂
  have hND : ∀ s : ℂ, s.re < -r + 1 → (∏ v ∈ S, zetaIntegral (localHaar n v)
      (GJMatrix.localMatrixFourier (GroundTheory.Global.localAdelicChar K v) (Φ v))
      (fun g => Parabolic.matrixCoeff (F := v.adicCompletion K) (D.finite.π v) (x v) (ℓ v) g⁻¹) (1 - s)) =
      fac c₀ t q P₀ s := fun s hs => by
    rw [← hfac]
    refine Finset.prod_congr rfl fun v hv => (hd v hv).2.2.2 s ?_
    have := Finset.single_le_sum (f := fun v => |cv v|) (fun _ _ => abs_nonneg _) hv
    linarith [le_abs_self (cv v)]
  refine ⟨linPoly (∑ τ, m τ), (monic_multiset_prod_of_monic _ _ fun z _ => monic_X_add_C z).ne_zero,
    Λ, fun s => Λ' (s + 1), fun s => c * archZeta Measure.haar φ fi s * ∏ v ∈ S, b v,
    fun s => c' * archZeta Measure.haar (archMatrixFourier φ) (fun y => fi y⁻¹) (1 - s),
    k, k', c₀, t, r, hΛ, hΛ'.comp (differentiable_id.add_const 1), ?_, hk, hk', fun s hs => ⟨?_, ?_⟩,
    fun s hs => ⟨?_, ?_⟩⟩
  · obtain ⟨s, hs, hA⟩ := far_ne hAd hA0 σ₁
    intro e
    have := (h1 s hs).2.1
    rw [e, hloc] at this
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero hc hA) hb') (h1 s hs).1 this.symm
  · rw [(h1 s (by linarith)).2.1, hloc, hL]
    ring
  · beta_reduce
    rw [(h2 (s + 1) (by simp; linarith)).2.1, hloc, hL, hsh]
    ring
  · have := (h1 (1 - s) (by simp; linarith)).2.2
    rw [sub_sub_cancel, hL', hND s (by linarith)] at this
    rw [this]
    ring
  · have := (h2 (1 - (s + 1)) (by simp; linarith)).2.2
    rw [sub_sub_cancel, hL', hND (s + 1) (by simp; linarith), hsh', show 1 - (s + 1) + 1 = 1 - s by ring] at this
    beta_reduce
    rw [this]
    ring
