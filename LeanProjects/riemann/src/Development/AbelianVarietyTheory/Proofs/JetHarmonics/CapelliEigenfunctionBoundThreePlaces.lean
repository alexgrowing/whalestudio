import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.SupWOfSup
import Development.AbelianVarietyTheory.PublishedTheorems.BesselIntegrals.BesselXiIntegrable
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Cut_BPEq
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutLimENF
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutBPEqNF
import Formalism.HermitianCurvature.HerGenC
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.JetBoundEqualTypesThreePlacesOfXiIntegrableStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.TendstoLevelZeroFormCutoffPowMulOfDominationStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.LevelZeroEnergyBoundDecayingCasimirEigenfunctionStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LatticeSumOfCompactCoefficientPositivityStatement
open BpJoin Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutBP Formalism.FourierDecayAlt.P.CutBP2 Formalism.FourierDecayAlt.P.CutBPEq Formalism.QuantumDeterminants

namespace GlobalTheory.EigenThreePlaces

theorem exists_isCut0 : ∃ χ : ℝ → ℝ, C6.IsCut0 χ := by
  refine ⟨fun x => Real.smoothTransition (2 * x - 1), ?_, ⟨1 / 2, by norm_num, fun x hx => ?_⟩, fun x hx => ?_⟩
  · exact Real.smoothTransition.contDiff.comp ((contDiff_const.mul contDiff_id).sub contDiff_const)
  · exact Real.smoothTransition.zero_of_nonpos (by linarith)
  · exact Real.smoothTransition.one_of_one_le (by linarith)

theorem decay_split (c c' x : ℝ) (k r N : ℕ)
    (h : max 3 (max c c') * ((r : ℝ) + 1) ^ 4 *
      ((N : ℝ) * (2 * (r : ℝ) + k + 1) ^ 2 + (2 * (r : ℝ) + k + 1) ^ 3) ≤ x) :
    c * ((r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (r : ℝ) + k + 1) ^ 2 + (2 * (r : ℝ) + k + 1) ^ 3) ≤ x ∧
      c' * ((r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (r : ℝ) + k + 1) ^ 2 + (2 * (r : ℝ) + k + 1) ^ 3) ≤ x ∧
      B.AB k r ≤ x := by
  have hr : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  set n : ℝ := 2 * (r : ℝ) + k + 1 with hn
  have hn1 : 1 ≤ n := by linarith
  have hX : 0 ≤ (N : ℝ) * n ^ 2 + n ^ 3 := by positivity
  have hR : 0 ≤ ((r : ℝ) + 1) ^ 4 := by positivity
  refine ⟨le_trans ?_ h, le_trans ?_ h, le_trans ?_ h⟩
  · gcongr
    exact (le_max_left _ _).trans (le_max_right _ _)
  · gcongr
    exact (le_max_right _ _).trans (le_max_right _ _)
  · have h1 : (r : ℝ) + 1 ≤ ((r : ℝ) + 1) ^ 4 := le_self_pow₀ (by linarith) (by norm_num)
    have h2 : n ≤ n ^ 3 := le_self_pow₀ hn1 (by norm_num)
    have h3 : n ≤ (N : ℝ) * n ^ 2 + n ^ 3 := by
      have : 0 ≤ (N : ℝ) * n ^ 2 := by positivity
      linarith
    calc B.AB k r ≤ 3 * ((r : ℝ) + 1) * n := by
          unfold B.AB
          rw [hn]
          nlinarith [mul_nonneg hr hk, mul_nonneg hr hr]
      _ ≤ _ := by
          gcongr
          exact le_max_left _ _

theorem main : GlobalTheory.HCXi.BesselXiIntegrable → P5.ThmPActualCpt → NFTopDomAll → ∀ Cb C₃ CΛ C₀ : ℝ, 0 ≤ C₃ → 0 ≤ CΛ → 0 ≤ C₀ → ∃ C₄ Cc : ℝ, ∀ (P : M.Par) (Wp Wq Wqp Wqm : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] [NormedAddCommGroup Wqp] [InnerProductSpace ℂ Wqp] [FiniteDimensional ℂ Wqp] [NormedAddCommGroup Wqm] [InnerProductSpace ℂ Wqm] [FiniteDimensional ℂ Wqm] (up up' um um' : ℕ → ℝ) (p : KB.Pl P Wp Wq) (pp : KB.Pl (shP P up up') Wp Wqp) (pm : KB.Pl (shP P um um') Wp Wqm) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Ap : B.Mat P.k P.r → (Wqp →L[ℂ] Wq)) (Am : B.Mat P.k P.r → (Wqm →L[ℂ] Wq)) (ApPt : C.LPt → (Wqp →L[ℂ] Wq)) (AmPt : C.LPt → (Wqm →L[ℂ] Wq)) (b Λ A₀ : ℝ) (n₀ p₀ d : ℕ) (nnp nnm : ℝ → ℝ) (Yp Ym : Finset ℝ) (K N : ℕ), 3 ≤ b → 1 ≤ Λ → Λ ≤ b ^ (CΛ * ((2 * P.r + 2 : ℕ) : ℝ)) → n₀ ≤ 30 * (P.r + 1) ^ 2 + 6 → (p₀ : ℝ) ≤ C₀ * ((P.r : ℝ) + 1) ^ 2 → pp.T.base.z = p.T.base.z → pp.T.base.z' = p.T.base.z' → pm.T.base.z = p.T.base.z → pm.T.base.z' = p.T.base.z' → 3 ≤ K → (P.r + 1) * K ≤ N → (∀ y, 0 < nnp y) → (∀ y, 0 < nnm y) → KB.InDDplus2 (shP P up up') pp.l0 pp.T.base Cb pp.Θ → KB.InDDplus2 (shP P um um') pm.l0 pm.T.base Cb pm.Θ → B.CkOn ⊤ (B.GV P.k P.r) f → (∀ m : ℕ, B.InCC A₀ m f) → CutBPEq.PolyOp d Ap → CutBPEq.PolyOp d Am → Cc * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤ A₀ - (((2 * P.r + 2) * p₀ : ℕ) : ℝ) - d → AmapsSh p pp pm f Ap Am ApPt AmPt b n₀ → TBB.RegularityBoundBigCell p f b C₃ (2 * p₀ + n₀) → TBBx5.WaveGrid pp nnp Yp Λ K N → TBBx5.LiftGrid pp nnp Yp Λ K N → TBBx5.WaveGrid pm nnm Ym Λ K N → TBBx5.LiftGrid pm nnm Ym Λ K N → N ≤ 2 * p₀ → ∀ (lam lam' : Fin (2 * P.r + P.k + 1) → ℝ) (cs : ℝ), (∀ y : ℝ, ∀ g ∈ B.GV P.k P.r, Q.CV P.k P.r (y : ℂ) f g = ((∏ s, (y + lam' s) : ℝ) : ℂ) • f g) → (∀ s t, s ≠ t → 2 * cs ≤ |lam s - lam t|) → (∀ s, |lam' s - lam s| + (((2 * P.r + 2) * p₀ + d : ℕ) : ℝ) ≤ cs - 1) → (∀ y : ℝ, ∏ s, (|y + lam s| + cs) ≤ nnp y) → (∀ y : ℝ, ∏ s, (|y + lam s| + cs) ≤ nnm y) → TBB.ThmBpAt p f b C₄ n₀ p₀ := by
  intro hX hP hDom Cb C₃ CΛ C₀ hC₃ hCΛ hC₀
  obtain ⟨C₄, Cc, h⟩ := GlobalTheory.T.jetBound_equalTypes_threePlaces_of_xiIntegrable hX hP Cb C₃ CΛ C₀ hC₃ hCΛ hC₀
  obtain ⟨Cn, hn⟩ := GlobalTheory.T.tendsto_levelZero_form_cutoff_pow_mul_of_domination hX hP hDom Cb
  obtain ⟨-, L2⟩ := GlobalTheory.T.levelZeroEnergyBound_decayingCasimirEigenfunction hX
  obtain ⟨χ, hχ⟩ := exists_isCut0
  refine ⟨C₄, max 3 (max Cc Cn), ?_⟩
  intro P Wp Wq Wqp Wqm _ _ _ _ _ _ _ _ _ _ _ _ up up' um um' p pp pm f Ap Am ApPt AmPt b Λ A₀ n₀ p₀ d
    nnp nnm Yp Ym K N hb hΛ hΛb hn₀ hp₀ hzp hzp' hzm hzm' hK hKN hnnp hnnm hDDp hDDm hf hfA hAp hAm
    hth hAms hreg hWGp hLGp hWGm hLGm hN2 lam lam' cs he hs hc hnp hnm
  obtain ⟨hth1, hth4, hth3⟩ := decay_split Cc Cn _ P.k P.r N hth
  have hth4' : Cn * ((P.r : ℝ) + 1) ^ 4 *
      ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤
      (A₀ - d) - (((2 * P.r + 2) * p₀ : ℕ) : ℝ) := by linarith
  have hA3 : B.AB P.k P.r ≤ A₀ - (((2 * P.r + 2) * p₀ + d : ℕ) : ℝ) := by
    rw [Nat.cast_add]; linarith
  have hLp : LimEvT pp χ (fpmSh pp f Ap p₀) Yp N := by
    have e := fpmSh_eq_fpm pp f Ap p₀
    have k := hn Wp Wqp (shP P up up') pp (fun g => (f g).comp (Ap g)) (A₀ - d) p₀ χ Yp N
      ⟨hχ, hDDp, ckOn_compSh hf (ckOn_of_polyOp hAp), inCC_compSh pp hfA hAp, hth4', hN2⟩
    exact Eq.mpr (congrArg (fun F => LimEvT pp χ F Yp N) e) k
  have hLm : LimEvT pm χ (fpmSh pm f Am p₀) Ym N := by
    have e := fpmSh_eq_fpm pm f Am p₀
    have k := hn Wp Wqm (shP P um um') pm (fun g => (f g).comp (Am g)) (A₀ - d) p₀ χ Ym N
      ⟨hχ, hDDm, ckOn_compSh hf (ckOn_of_polyOp hAm), inCC_compSh pm hfA hAm, hth4', hN2⟩
    exact Eq.mpr (congrArg (fun F => LimEvT pm χ F Ym N) e) k
  have hI5p : ∀ ε : ℝ, 0 < ε → ∀ n : ℕ,
      TBB.BlockGrowthBound pp nnp (apx (D.cutF pp.T.base χ (fpmSh pp f Ap p₀) ε) n) Yp K N := fun ε hε n =>
    GlobalTheory.T.latticeSum_of_compactCoefficient_positivity hP Wp Wqp (shP P up up') pp nnp _ Yp K N Cb hDDp
      (cptCoef_apx (shP P up up') pp.T.base hχ (ckOn_fpmSh pp p₀ hf (ckOn_of_polyOp hAp)) hε n) hnnp
  have hI5m : ∀ ε : ℝ, 0 < ε → ∀ n : ℕ,
      TBB.BlockGrowthBound pm nnm (apx (D.cutF pm.T.base χ (fpmSh pm f Am p₀) ε) n) Ym K N := fun ε hε n =>
    GlobalTheory.T.latticeSum_of_compactCoefficient_positivity hP Wp Wqm (shP P um um') pm nnm _ Ym K N Cb hDDm
      (cptCoef_apx (shP P um um') pm.T.base hχ (ckOn_fpmSh pm p₀ hf (ckOn_of_polyOp hAm)) hε n) hnnm
  exact h P Wp Wq Wqp Wqm up up' um um' p pp pm f Ap Am ApPt AmPt b Λ A₀ n₀ p₀ d
    χ nnp nnm Yp Ym K N hb hΛ hΛb hn₀ hp₀ hzp hzp' hzm hzm' hK hKN hχ hnnp hnnm hDDp hDDm hf hfA hAp hAm
    hth1 hAms hreg hWGp hLGp hWGm hLGm hI5p hI5m hLp hLm
    (L2 Wp Wq Wqp P up up' pp lam lam' cs A₀ p₀ d nnp f Ap Yp N hAp hf hfA he hs hc hA3 hnp)
    (L2 Wp Wq Wqm P um um' pm lam lam' cs A₀ p₀ d nnm f Am Ym N hAm hf hfA he hs hc hA3 hnm)

end GlobalTheory.EigenThreePlaces
