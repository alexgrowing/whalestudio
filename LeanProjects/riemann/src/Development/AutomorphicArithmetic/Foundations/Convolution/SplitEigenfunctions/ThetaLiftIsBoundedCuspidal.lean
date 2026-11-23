import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.ThetaLiftEqAnisotropicPart
import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.SzLaws
import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.ContinuousPrN
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.ImportsRest
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.Iwa
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AutomorphicFormGLContinuous
import GroundTheory.AutomorphicForms.CompactFormulaCountable
import GroundTheory.GlobalFields.TateThesis.IdeleMeasureQuotient

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical

namespace UpperTheory.ConvolutionTheory.RankTwoDescent.FundamentalDomainContinuity

private theorem cont_nested {X Z Y : Type} [TopologicalSpace X] [FirstCountableTopology X]
    [TopologicalSpace Z] [SecondCountableTopology Z] [MeasurableSpace Z] [BorelSpace Z]
    [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (μ : Measure Z) (ν : Measure Y) (S : Set Z) (Dm : Set Y) (hS : MeasurableSet S) (hμ : μ S < ⊤) (hν : ν Dm < ⊤)
    (f : X → Z → Y → ℂ) (x₀ : X) (U : Set X) (hU : U ∈ 𝓝 x₀) (B : ℝ)
    (hb : ∀ x ∈ U, ∀ z ∈ closure S, ∀ y, ‖f x z y‖ ≤ B)
    (hc : ∀ y, Continuous fun p : X × Z => f p.1 p.2 y)
    (hy : ∀ x z, Continuous (f x z)) :
    ContinuousAt (fun x => ∫ z in S, ∫ y in Dm, f x z y ∂ν ∂μ) x₀ := by
  have hint : Integrable (fun _ : Y => B) (ν.restrict Dm) := integrableOn_const hν.ne
  have hG : ∀ x ∈ U, ContinuousOn (fun z => ∫ y in Dm, f x z y ∂ν) (closure S) := by
    intro x hx z₀ hz₀
    refine tendsto_integral_filter_of_dominated_convergence (fun _ => B) ?_ ?_ hint ?_
    · exact Eventually.of_forall fun z => (hy x z).aestronglyMeasurable
    · exact eventually_nhdsWithin_of_forall fun z hz => Eventually.of_forall fun y => hb x hx z hz y
    · refine Eventually.of_forall fun y => ?_
      have h1 : Continuous fun z => f x z y := (hc y).comp (Continuous.prodMk_right x)
      exact h1.continuousWithinAt
  refine tendsto_integral_filter_of_dominated_convergence (fun _ => B * ν.real Dm) ?_ ?_ (integrableOn_const hμ.ne) ?_
  · filter_upwards [hU] with x hx
    exact ((hG x hx).aestronglyMeasurable isClosed_closure.measurableSet).mono_measure
      (Measure.restrict_mono subset_closure le_rfl)
  · filter_upwards [hU] with x hx
    refine ae_restrict_of_forall_mem hS fun z hz => ?_
    exact norm_setIntegral_le_of_norm_le_const hν fun y _ => hb x hx z (subset_closure hz) y
  · refine ae_restrict_of_forall_mem hS fun z hz => ?_
    refine tendsto_integral_filter_of_dominated_convergence (fun _ => B) ?_ ?_ hint ?_
    · exact Eventually.of_forall fun x => (hy x z).aestronglyMeasurable
    · filter_upwards [hU] with x hx
      exact Eventually.of_forall fun y => hb x hx z (subset_closure hz) y
    · refine Eventually.of_forall fun y => ?_
      have h1 : Continuous fun x => f x z y := (hc y).comp (Continuous.prodMk_left z)
      exact h1.continuousAt

variable {E : Type} [Field E] [NumberField E]

private theorem norm_liftIntegral_le (D : Dat ℚ E) (N : MeasE E) (hV : N.μ N.D < ⊤) (Ψ : GL (Fin 2) (A E) → ℂ) (B : ℝ)
    (hB : ∀ z ∈ normOneFundamentalDomain E, ∀ h : G1 E, ‖Ψ (gl h * sZ D (z : IdeleGroup E))‖ ≤ B) :
    ‖J1 D N Ψ‖ ≤ B * N.μ.real N.D * (normOneMeasure E).real (normOneFundamentalDomain E) := by
  unfold J1 UI
  refine norm_setIntegral_le_of_norm_le_const (normOneMeasure_normOneFundamentalDomain_lt_top E) fun z hz => ?_
  unfold mean
  exact norm_setIntegral_le_of_norm_le_const hV fun h _ => hB z hz h

end UpperTheory.ConvolutionTheory.RankTwoDescent.FundamentalDomainContinuity

open UpperTheory.ConvolutionTheory.RankTwoDescent.FundamentalDomainContinuity in
theorem UpperTheory.ConvolutionTheory.RankTwoDescent.thetaPairing_constantTerm_cuspidal :
    Maj → ThCont → ThetaLiftEqAnisotropicPart → Coef → ThetaLiftIsBoundedCuspidal := by
  intro hMaj hTh hF0 hCoef E _ _ _ D W M N P ph hph φ hφ
  obtain ⟨-, hsC, hsN, hgN, -, -, -, -, -, -, -⟩ := szLaws E D
  have hφc : Continuous φ.1 := IsAutForm.continuous (P.cusp φ hφ).1
  have hV : N.μ N.D < ⊤ := volE E N
  set Zc : Set ↥(IdeleGroup.normOneSubgroup E) := closure (normOneFundamentalDomain E) with hZc
  have hZcpt : IsCompact Zc := isCompact_closure_normOneFundamentalDomain E
  have hsz : Continuous fun z : ↥(IdeleGroup.normOneSubgroup E) => sZ D (z : IdeleGroup E) :=
    hsC.comp continuous_subtype_val
  set C : Set (GL (Fin 2) (A E)) := (fun z : ↥(IdeleGroup.normOneSubgroup E) => sZ D (z : IdeleGroup E)) '' Zc with hCdef
  have hC : IsCompact C := hZcpt.image hsz
  have hCn : ∀ k ∈ C, nu ℚ k = 1 := by
    rintro k ⟨z, -, rfl⟩
    exact hsN _
  have hzC : ∀ z ∈ Zc, sZ D (z : IdeleGroup E) ∈ C := fun z hz => ⟨z, hz, rfl⟩
  have hleft : LInv (f0 W N ph φ.1) := by
    intro γ g
    simp only [f0, map_mul, Module.End.mul_apply, W.th_Om]
  have hth := hTh E D W M N P ph hph Set.univ
  have eTh : ∀ u : V4 ℚ → ℂ, ThOn Set.univ u = Th u := fun u => tsum_univ (fun ξ : Fin 4 → ℚ => u (rp ξ))
  have hnu : ∀ (h : G1 E) (z : (A E)ˣ), (gl h * sZ D z) ∈ {x : GL (Fin 2) (A E) | nu ℚ x = 1} := by
    intro h z
    have a1 : ideleNorm ℚ E (Matrix.GeneralLinearGroup.det (gl h)) = 1 := hgN h
    have a2 : ideleNorm ℚ E (Matrix.GeneralLinearGroup.det (sZ D z)) = 1 := hsN z
    change ideleNorm ℚ E (Matrix.GeneralLinearGroup.det (gl h * sZ D z)) = 1
    rw [map_mul, map_mul, a1, a2, one_mul]
  refine ⟨?_, hleft, ?_, ?_⟩
  ·
    refine continuous_iff_continuousAt.2 fun g₀ => ?_
    obtain ⟨U, hUc, hU⟩ := exists_compact_mem_nhds g₀
    obtain ⟨-, hIw⟩ := UpperTheory.ConvolutionTheory.R2.Ff.iwa ℚ
    obtain ⟨V, hVc, hVU⟩ := hIw U hUc
    have hab : Continuous (ab : (A ℚ)ˣ → ℝ) := UpperTheory.ConvolutionTheory.R2.continuous_ab
    have hpos : ∀ a : (A ℚ)ˣ, 0 < ab a := fun a => (IdeleGroup.ideleModule ℚ a).2
    obtain ⟨T, hT⟩ := hVc.exists_bound_of_continuousOn hab.continuousOn
    obtain ⟨T', hT'⟩ := hVc.exists_bound_of_continuousOn
      (f := fun a => (ab a)⁻¹) (hab.inv₀ fun a => (hpos a).ne').continuousOn
    have hc0 : 0 < (|T'| + 1)⁻¹ := inv_pos.2 (by positivity)
    obtain ⟨B, hB⟩ := hMaj E D W M N P ph hph φ hφ C hC hCn _ hc0 0
    refine cont_nested (normOneMeasure E) N.μ (normOneFundamentalDomain E) N.D
      (measurableSet_normOneFundamentalDomain E) (normOneMeasure_normOneFundamentalDomain_lt_top E) hV
      (fun g z h => Th (W.Om g (W.L (gl h * sZ D (z : IdeleGroup E)) ph)).1 * φ.1 (gl h * sZ D (z : IdeleGroup E)))
      g₀ U hU (|B| * T ^ 2) ?_ ?_ ?_
    · intro x hx z hz h
      obtain ⟨b, a, ha, k, hk, rfl⟩ := hVU x hx
      have hle : (|T'| + 1)⁻¹ ≤ ab a := by
        have h1 : (ab a)⁻¹ ≤ |T'| + 1 := by
          have := hT' a ha
          rw [Real.norm_eq_abs, abs_of_pos (inv_pos.2 (hpos a))] at this
          linarith [le_abs_self T']
        exact (inv_le_comm₀ (hpos a) (by positivity)).1 h1
      obtain ⟨h1, h2, -⟩ := hB b a k hk hle h _ (hzC z hz)
      have h3 : ab a ≤ T := by
        have := hT a ha
        rwa [Real.norm_eq_abs, abs_of_pos (hpos a)] at this
      rw [norm_mul]
      calc _ ≤ _ := mul_le_mul_of_nonneg_right (norm_tsum_le_tsum_norm h1) (norm_nonneg _)
        _ ≤ _ := h2
        _ ≤ |B| * T ^ 2 := mul_le_mul (le_abs_self B)
          (pow_le_pow_left₀ (hpos a).le h3 2) (by have := hpos a; positivity) (abs_nonneg B)
    · intro y
      have hA : Continuous fun p : G1 ℚ × ↥(IdeleGroup.normOneSubgroup E) => (p.1, gl y * sZ D (p.2 : IdeleGroup E)) :=
        continuous_fst.prodMk (continuous_const.mul (hsz.comp continuous_snd))
      have h1 := hth.comp_continuous hA (fun p => hnu y _)
      simp only [eTh] at h1
      exact h1.mul (hφc.comp (continuous_const.mul (hsz.comp continuous_snd)))
    · intro x z
      have hA : Continuous fun h : G1 E => (x, gl h * sZ D (z : IdeleGroup E)) :=
        continuous_const.prodMk (UpperTheory.ConvolutionTheory.R2.continuous_gl.mul continuous_const)
      have h1 := hth.comp_continuous hA (fun h => hnu h _)
      simp only [eTh] at h1
      exact h1.mul (hφc.comp (UpperTheory.ConvolutionTheory.R2.continuous_gl.mul continuous_const))
  ·
    obtain ⟨c, hc, hred⟩ := red ℚ
    obtain ⟨B, hB⟩ := hMaj E D W M N P ph hph φ hφ C hC hCn c hc 0
    refine ⟨B * N.μ.real N.D * (normOneMeasure E).real (normOneFundamentalDomain E), fun g => ?_⟩
    obtain ⟨γ, b, a, k, hk, he, hle⟩ := hred g
    rw [← hleft γ g, he, hF0 E D W M N P ph hph φ hφ]
    refine norm_liftIntegral_le D N hV _ B fun z hz h => ?_
    obtain ⟨h1, -, h3⟩ := hB b a k hk hle h _ (hzC z (subset_closure hz))
    have h4 : ‖ThOn {ξ | qr D.δ ξ ≠ 0} (W.Om (nU b * mD a * k) (W.L (gl h * sZ D (z : IdeleGroup E)) ph)).1‖ ≤
        ∑' ξ : {ξ : Fin 4 → ℚ // qr D.δ ξ ≠ 0},
          ‖(W.Om (nU b * mD a * k) (W.L (gl h * sZ D (z : IdeleGroup E)) ph)).1 (rp ξ.1)‖ :=
      norm_tsum_le_tsum_norm (h1.subtype _)
    rw [norm_mul]
    refine (mul_le_mul_of_nonneg_right h4 (norm_nonneg _)).trans ?_
    simpa using h3
  ·
    intro g
    have h := hCoef E D W M N P ph hph φ hφ 0 g
    have e0 : fOn W N {ξ | qr D.δ ξ ≠ 0 ∧ qr D.δ ξ = 0} ph φ.1 g = 0 := by
      have e : {ξ : Fin 4 → ℚ | qr D.δ ξ ≠ 0 ∧ qr D.δ ξ = 0} = ∅ := by
        ext ξ
        simp
      rw [e]
      simp [fOn, J1, UI, mean, ThOn]
    have e1 : ∀ b : A ℚ, ψ (-(b * UpperTheory.ConvolutionTheory.R2.rt (0 : ℚ))) = 1 := fun b => by simp [ψ, UpperTheory.ConvolutionTheory.R2.rt]
    rw [e0, mul_zero] at h
    simp only [e1, mul_one] at h
    rw [hF0 E D W M N P ph hph φ hφ]
    exact h
