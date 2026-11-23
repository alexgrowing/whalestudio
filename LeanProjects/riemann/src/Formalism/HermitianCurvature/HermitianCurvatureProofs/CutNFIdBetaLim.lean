import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutNFId
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutDomCutInt
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutFpmDecay

namespace Formalism.FourierDecayAlt.P.CutBP

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology MeasureTheory

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem hsVec_ofReal_smul {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (c : ℝ) (X : Wq →L[ℂ] Wp) :
    B.hsVec ((c : ℂ) • X) = (c : ℂ) • B.hsVec X := by
  unfold B.hsVec
  rfl

theorem nfBetaLim_thr (R K Nn A : ℝ) (hR : 0 ≤ R) (hK : 0 ≤ K) (hN : 0 ≤ Nn)
    (h : 10 * (R + 1) ^ 4 * (Nn * (2 * R + K + 1) ^ 2 + (2 * R + K + 1) ^ 3) ≤ A) :
    2 * (K + R) * (R + 1) + 1 ≤ A ∧ (2 * R + K + 1) ^ 2 < A / (9 * (R + 1)) := by
  set n := 2 * R + K + 1 with hn
  have hn1 : 1 ≤ n := by rw [hn]; linarith
  have h4 : R + 1 ≤ (R + 1) ^ 4 := le_self_pow₀ (by linarith) (by norm_num)
  have hn3 : n ^ 2 ≤ n ^ 3 := pow_le_pow_right₀ hn1 (by norm_num)
  have a1 : (R + 1) * n ^ 2 ≤ (R + 1) ^ 4 * n ^ 3 := mul_le_mul h4 hn3 (by positivity) (by positivity)
  have a2 : (R + 1) ^ 4 * n ^ 3 ≤ (R + 1) ^ 4 * (Nn * n ^ 2 + n ^ 3) :=
    mul_le_mul_of_nonneg_left (by nlinarith [sq_nonneg n]) (by positivity)
  have key : 10 * ((R + 1) * n ^ 2) ≤ A := by
    have e : 10 * (R + 1) ^ 4 * (Nn * n ^ 2 + n ^ 3) = 10 * ((R + 1) ^ 4 * (Nn * n ^ 2 + n ^ 3)) := by ring
    rw [e] at h
    linarith
  have hpos : 0 < (R + 1) * n ^ 2 := by positivity
  refine ⟨?_, ?_⟩
  · have hnn : n ≤ n ^ 2 := by nlinarith
    have b1 : 2 * (K + R) * (R + 1) + 1 ≤ 2 * n * (R + 1) := by rw [hn]; nlinarith
    have b2 : 2 * n * (R + 1) ≤ 2 * ((R + 1) * n ^ 2) := by nlinarith
    linarith
  · rw [lt_div_iff₀ (by positivity)]
    nlinarith

section place

variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem truncated_pairing_eq_integral (p : KB.Pl P Wp Wq) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (χ : ℝ → ℝ) (ε : ℝ)
    (w : List C.Letter) :
    pair0 p F (D.cutF p.T.base χ F ε) w =
      ∫ q, ((χ (Gf P.k P.r p.T.base.z p.T.base.z' (bigCell P.k P.r q.1 (p.T.base.μsec q.2)) / ε) : ℝ) : ℂ) *
        levelZeroRadialIntegral p w F q := by
  unfold pair0 B.beta betaBig
  refine integral_congr_ae (Eventually.of_forall fun q => ?_)
  show (bcWeight P.k P.r (Tz P.k P.r p.T.base.z) (Tz P.k P.r p.T.base.z') q : ℂ) *
      inner ℂ (B.hsVec (B.JF p.T.base (D.cutF p.T.base χ F ε) (bigCell P.k P.r q.1 (p.T.base.μsec q.2))))
        (B.hsVec (B.JF p.T.base (w.foldr (fun a H => M.sgn P p.l0 • Q.CV P.k P.r (a.2 : ℂ) H) F)
          (bigCell P.k P.r q.1 (p.T.base.μsec q.2)))) = _
  rw [Formalism.FourierDecayAlt.P.JCTx2.JF_cutF, hsVec_ofReal_smul, inner_smul_left, Complex.conj_ofReal]
  unfold levelZeroRadialIntegral
  ring

theorem self_pairing_eq_integral (p : KB.Pl P Wp Wq) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (w : List C.Letter) :
    pair0 p F F w = ∫ q, levelZeroRadialIntegral p w F q := by
  unfold pair0 B.beta betaBig
  rfl

end place

theorem beta_limit_all_levels_holds : NFBetaLimAll := by
  intro Cb
  refine ⟨10, ?_⟩
  intro Wp Wq _ _ _ _ _ _ P p f A₀ p₀ χ Y N hH w hw hN
  obtain ⟨hχ, -, -, hfA, hth, -⟩ := hH
  obtain ⟨δ, hδ, hχ0⟩ := hχ.2.1
  set F' := TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀ with hF'
  set A := A₀ - (((2 * P.r + 2) * p₀ : ℕ) : ℝ) with hAdef
  have hCC : ∀ m : ℕ, B.InCC A m F' := inCC_fpm_id p p₀ hfA
  obtain ⟨hAB', hT'⟩ := nfBetaLim_thr (P.r : ℝ) (P.k : ℝ) (N : ℝ) A (by positivity) (by positivity) (by positivity) hth
  have hAB : B.AB P.k P.r ≤ A := by unfold B.AB; exact hAB'
  have hT : JF.TransportedAlt P.k P.r A 0 := by
    unfold JF.TransportedAlt
    push_cast
    simpa using hT'
  set Ds := p.T.base with hDs
  have hI : Integrable (levelZeroRadialIntegral p w F') := rr0Int_integrable p w hAB hT fun j _ => hCC j

  obtain ⟨Cχ, hCχ⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    hχ.1.continuous.continuousOn
  set Mχ := max Cχ 1 with hMdef
  have hM : ∀ x, ‖χ x‖ ≤ Mχ := by
    intro x
    rcases lt_or_ge x 0 with h | h
    · rw [hχ0 x (by linarith), norm_zero]; exact le_max_of_le_right zero_le_one
    rcases le_or_gt x 1 with h' | h'
    · exact (hCχ x ⟨h, h'⟩).trans (le_max_left _ _)
    · rw [hχ.2.2 x h'.le, norm_one]; exact le_max_right _ _

  set K := Formalism.FourierDecayAlt.P.CutMP.En.foldCV P.k P.r (M.sgn P p.l0) w F' with hK
  have hK0 : B.InCC A 0 K :=
    Formalism.FourierDecayAlt.P.CutMP.En.inCC_fold Formalism.FourierDecayAlt.P.CutMP.En.coefficient_vector_in_L2_class A (M.sgn P p.l0) F' w 0 (hCC _)
  have cH' := jgq_continuousOn Ds hT (hCC 0)
  have cK' := jgq_continuousOn Ds hT hK0
  have hcv := Formalism.FourierDecayAlt.P.CutMP.En.hsVec_contDiff (V := Wp) (W := Wq)
  have ca : ContinuousOn (fun q => B.hsVec (B.JF Ds F' (B.gq Ds q))) (JF.QDom P.k P.r Ds.z Ds.z') :=
    hcv.continuous.comp_continuousOn cH'
  have cb : ContinuousOn (fun q => B.hsVec (B.JF Ds K (B.gq Ds q))) (JF.QDom P.k P.r Ds.z Ds.z') :=
    hcv.continuous.comp_continuousOn cK'
  have hgq : ContinuousOn (fun q => B.gq Ds q) (JF.QDom P.k P.r Ds.z Ds.z') :=
    (Formalism.FourierDecayAlt.P.BigCellOpenDomain.gq_contDiffOn Ds 0).continuousOn
  have hmeas : ∀ ε : ℝ, AEStronglyMeasurable (fun q =>
      ((χ (Gf P.k P.r Ds.z Ds.z' (bigCell P.k P.r q.1 (Ds.μsec q.2)) / ε) : ℝ) : ℂ) * levelZeroRadialIntegral p w F' q) volume := by
    intro ε
    have cχ : ContinuousOn (fun q => ((χ (Gf P.k P.r Ds.z Ds.z' (B.gq Ds q) / ε) : ℝ) : ℂ))
        (JF.QDom P.k P.r Ds.z Ds.z') :=
      Complex.continuous_ofReal.comp_continuousOn (hχ.1.continuous.comp_continuousOn
        (((Formalism.FourierDecayAlt.P.JCx1.contDiff_Gf Ds.z Ds.z').continuous.comp_continuousOn hgq).div_const ε))
    have := aesm_weight_smul Ds (cχ.mul (ca.inner cb))
    refine this.congr (Eventually.of_forall fun q => ?_)
    show (bcWeight P.k P.r (Tz P.k P.r Ds.z) (Tz P.k P.r Ds.z') q : ℝ) • (((χ (Gf P.k P.r Ds.z Ds.z' (B.gq Ds q) / ε) : ℝ) : ℂ) *
      inner ℂ (B.hsVec (B.JF Ds F' (B.gq Ds q))) (B.hsVec (B.JF Ds K (B.gq Ds q)))) = _
    rw [Complex.real_smul]
    show _ = ((χ (Gf P.k P.r Ds.z Ds.z' (B.gq Ds q) / ε) : ℝ) : ℂ) *
      ((bcWeight P.k P.r (Tz P.k P.r Ds.z) (Tz P.k P.r Ds.z') q : ℂ) *
        inner ℂ (B.hsVec (B.JF Ds F' (B.gq Ds q))) (B.hsVec (B.JF Ds K (B.gq Ds q))))
    ring

  have hlim : ∀ᵐ q : (Fin P.r → ℂ) × ℂ, Tendsto (fun ε : ℝ =>
      ((χ (Gf P.k P.r Ds.z Ds.z' (bigCell P.k P.r q.1 (Ds.μsec q.2)) / ε) : ℝ) : ℂ) * levelZeroRadialIntegral p w F' q) (𝓝[>] 0)
      (𝓝 (levelZeroRadialIntegral p w F' q)) := by
    refine Eventually.of_forall fun q => ?_
    by_cases hq : bcWeight P.k P.r (Tz P.k P.r Ds.z) (Tz P.k P.r Ds.z') q = 0
    · have h0 : levelZeroRadialIntegral p w F' q = 0 := by unfold levelZeroRadialIntegral; rw [hq]; simp
      simp only [h0, mul_zero]
      exact tendsto_const_nhds
    obtain ⟨-, hG⟩ := bigCell_pos p q hq
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [Ioo_mem_nhdsGT hG] with ε hε
    have h1 : 1 ≤ Gf P.k P.r Ds.z Ds.z' (bigCell P.k P.r q.1 (Ds.μsec q.2)) / ε := by
      rw [le_div_iff₀ hε.1]; linarith [hε.2]
    rw [hχ.2.2 _ h1]
    simp
  have hT2 : Tendsto (fun ε : ℝ => ∫ q, ((χ (Gf P.k P.r Ds.z Ds.z' (bigCell P.k P.r q.1 (Ds.μsec q.2)) / ε) : ℝ) : ℂ) *
      levelZeroRadialIntegral p w F' q) (𝓝[>] 0) (𝓝 (∫ q, levelZeroRadialIntegral p w F' q)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun q => Mχ * ‖levelZeroRadialIntegral p w F' q‖)
      (Eventually.of_forall hmeas) (Eventually.of_forall fun ε => Eventually.of_forall fun q => ?_)
      (hI.norm.const_mul Mχ) hlim
    rw [norm_mul, Complex.norm_real]
    exact mul_le_mul_of_nonneg_right (hM _) (norm_nonneg _)
  have e1 : (fun ε : ℝ => (pair0 p F' (D.cutF p.T.base χ F' ε) w).re) =
      fun ε => (∫ q, ((χ (Gf P.k P.r Ds.z Ds.z' (bigCell P.k P.r q.1 (Ds.μsec q.2)) / ε) : ℝ) : ℂ) *
        levelZeroRadialIntegral p w F' q).re := funext fun ε => by rw [truncated_pairing_eq_integral]
  rw [e1, self_pairing_eq_integral]
  exact (Complex.continuous_re.tendsto _).comp hT2

end

end Formalism.FourierDecayAlt.P.CutBP
