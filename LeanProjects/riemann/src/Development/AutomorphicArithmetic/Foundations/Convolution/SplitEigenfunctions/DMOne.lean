import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.ThetaLiftEqAnisotropicPart
import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.SzLaws
import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.UnitsCpt
import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.ContinuousPrN
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.Vol
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.Iwa
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.ThMeas
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.ImportsRest
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.UnitsCpt
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnitaryActions.ContinuousAdelicGL2OfContinuousEntries

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical

namespace UpperTheory.ConvolutionTheory.RankTwoDescent

private theorem swap3 {X Y Z : Type} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
    (μ : Measure X) (ν : Measure Y) (ρ : Measure Z) [SFinite μ] [SFinite ν] [SFinite ρ]
    (H : X → Y → Z → ℂ) (hH : Integrable (fun p : X × Y × Z => H p.1 p.2.1 p.2.2) (μ.prod (ν.prod ρ))) :
    ∫ x, ∫ y, ∫ z, H x y z ∂ρ ∂ν ∂μ = ∫ y, ∫ z, ∫ x, H x y z ∂μ ∂ρ ∂ν := by
  have h1 : ∀ᵐ x ∂μ, ∫ y, ∫ z, H x y z ∂ρ ∂ν = ∫ q, H x q.1 q.2 ∂(ν.prod ρ) := by
    filter_upwards [hH.prod_right_ae] with x hx
    exact (integral_prod _ hx).symm
  rw [integral_congr_ae h1, ← integral_prod (fun p : X × Y × Z => H p.1 p.2.1 p.2.2) hH,
    integral_prod_symm _ hH]
  exact integral_prod (fun q : Y × Z => ∫ x, H x q.1 q.2 ∂μ) hH.integral_prod_right

private theorem dM_one' : dM (1 : (A ℚ)ˣ) = 1 := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [dM]

end UpperTheory.ConvolutionTheory.RankTwoDescent

theorem UpperTheory.ConvolutionTheory.RankTwoDescent.fub :
    Maj → ThCont → Fub := by
  intro hMaj hTh E _ _ _ D W M N P ph hph φ hφ π f hf
  obtain ⟨-, hsc, hnu, hnug, -⟩ := szLaws E D
  obtain ⟨c, hc, hred⟩ := UpperTheory.ConvolutionTheory.R2.red ℚ
  have hKc : IsCompact (KK ℚ) := (UpperTheory.ConvolutionTheory.R2.Ff.iwa ℚ).1
  have hC' : IsCompact (gl (F := ℚ) '' KK ℚ) := hKc.image continuous_gl
  obtain ⟨hfc, hdec⟩ := UpperTheory.ConvolutionTheory.R2.decay ℚ π f hf
  obtain ⟨B₂, hB₂⟩ := hdec _ hC' c hc 2
  set C : Set (GL (Fin 2) (A E)) :=
    (fun u : IdeleGroup.normOneSubgroup E => sZ D (u : IdeleGroup E)) '' closure (normOneFundamentalDomain E) with hCdef
  have hCc : IsCompact C :=
    (isCompact_closure_normOneFundamentalDomain E).image (hsc.comp continuous_subtype_val)
  have hCn : ∀ k ∈ C, nu ℚ k = 1 := by
    rintro _ ⟨u, -, rfl⟩
    exact hnu _
  obtain ⟨B₁, hB₁⟩ := hMaj E D W M N P ph hph φ hφ C hCc hCn c hc 0
  have hbound : ∀ (g : G1 ℚ) (h : G1 E), ∀ k ∈ C,
      ‖f.1 (gl g) * (Th (W.Om g (W.L (gl h * k) ph)).1 * φ.1 (gl h * k))‖ ≤ B₂ * B₁ := by
    intro g h k hk
    obtain ⟨γ, b, a, k', hk', hg, ha⟩ := hred g
    have hp : 0 < ab a := ab_pos a
    have e1 : f.1 (gl g) = f.1 (gl (nU b * mD a) * gl k') := by
      rw [← gl_mul, ← hg, gl_mul, gl_ratS, (π.cusp _ hf).1.left]
    have e2 : Th (W.Om g (W.L (gl h * k) ph)).1 = Th (W.Om (nU b * mD a * k') (W.L (gl h * k) ph)).1 := by
      rw [← hg]
      exact ((UpperTheory.ConvolutionTheory.R2.Ff.thMeas ℚ E D W (W.L (gl h * k) ph)).2.1 γ g).symm
    obtain ⟨hs, h2, -⟩ := hB₁ b a k' hk' ha h k hk
    have h1 := hB₂ b a (gl k') ⟨k', hk', rfl⟩ ha
    have h3 : ‖Th (W.Om (nU b * mD a * k') (W.L (gl h * k) ph)).1‖ ≤
        ∑' ξ : Fin 4 → ℚ, ‖(W.Om (nU b * mD a * k') (W.L (gl h * k) ph)).1 (rp ξ)‖ :=
      norm_tsum_le_tsum_norm hs
    rw [e1, e2, norm_mul, norm_mul]
    calc _ ≤ (B₂ * (ab a)⁻¹ ^ 2) * (B₁ * ab a ^ 2) :=
          mul_le_mul h1 ((mul_le_mul_of_nonneg_right h3 (norm_nonneg _)).trans h2)
            (mul_nonneg (norm_nonneg _) (norm_nonneg _)) ((norm_nonneg _).trans h1)
      _ = B₂ * B₁ := by field_simp
  have hφc : Continuous φ.1 := (UpperTheory.ConvolutionTheory.RankTwoDescent.decE E P φ hφ).1.1
  let H : G1 ℚ → IdeleGroup.normOneSubgroup E → G1 E → ℂ := fun g u h =>
    f.1 (gl g) * (Th (W.Om g (W.L (gl h * sZ D (u : IdeleGroup E)) ph)).1 * φ.1 (gl h * sZ D (u : IdeleGroup E)))
  have hx : Continuous fun p : G1 ℚ × IdeleGroup.normOneSubgroup E × G1 E =>
      gl p.2.2 * sZ D (p.2.1 : IdeleGroup E) :=
    (continuous_gl.comp (continuous_snd.comp continuous_snd)).mul
      (hsc.comp (continuous_subtype_val.comp (continuous_fst.comp continuous_snd)))
  have hnux : ∀ (h : G1 E) (u : IdeleGroup.normOneSubgroup E), nu ℚ (gl h * sZ D (u : IdeleGroup E)) = 1 := by
    intro h u
    rw [nu_mul, hnug, hnu, one_mul]
  have hTc : Continuous fun p : G1 ℚ × IdeleGroup.normOneSubgroup E × G1 E =>
      Th (W.Om p.1 (W.L (gl p.2.2 * sZ D (p.2.1 : IdeleGroup E)) ph)).1 := by
    have h0 := hTh E D W M N P ph hph Set.univ
    have h1 : Continuous fun p : G1 ℚ × IdeleGroup.normOneSubgroup E × G1 E =>
        ((p.1, gl p.2.2 * sZ D (p.2.1 : IdeleGroup E)) : G1 ℚ × GL (Fin 2) (A E)) := continuous_fst.prodMk hx
    have h2 := h0.comp_continuous h1 (fun p => hnux _ _)
    refine h2.congr fun p => ?_
    exact tsum_univ (fun ξ : Fin 4 → ℚ => (W.Om p.1 (W.L (gl p.2.2 * sZ D (p.2.1 : IdeleGroup E)) ph)).1 (rp ξ))
  have hHc : Continuous fun p : G1 ℚ × IdeleGroup.normOneSubgroup E × G1 E => H p.1 p.2.1 p.2.2 :=
    (hfc.comp (continuous_gl.comp continuous_fst)).mul (hTc.mul (hφc.comp hx))
  haveI : IsFiniteMeasure (M.μ.restrict M.D) := ⟨by simpa using UpperTheory.ConvolutionTheory.R2.Ff.vol ℚ M⟩
  haveI : IsFiniteMeasure ((normOneMeasure E).restrict (normOneFundamentalDomain E)) :=
    ⟨by simpa using normOneMeasure_normOneFundamentalDomain_lt_top E⟩
  haveI : IsFiniteMeasure (N.μ.restrict N.D) := ⟨by simpa using UpperTheory.ConvolutionTheory.RankTwoDescent.volE E N⟩
  have hae : ∀ᵐ p ∂((M.μ.restrict M.D).prod (((normOneMeasure E).restrict (normOneFundamentalDomain E)).prod
      (N.μ.restrict N.D))), p.2.1 ∈ normOneFundamentalDomain E := by
    have h1 : ∀ᵐ u ∂((normOneMeasure E).restrict (normOneFundamentalDomain E)), u ∈ normOneFundamentalDomain E :=
      ae_restrict_mem (measurableSet_normOneFundamentalDomain E)
    exact Measure.quasiMeasurePreserving_snd.ae (Measure.quasiMeasurePreserving_fst.ae h1)
  have hInt : Integrable (fun p : G1 ℚ × IdeleGroup.normOneSubgroup E × G1 E => H p.1 p.2.1 p.2.2)
      ((M.μ.restrict M.D).prod (((normOneMeasure E).restrict (normOneFundamentalDomain E)).prod (N.μ.restrict N.D))) := by
    refine Integrable.of_bound hHc.aestronglyMeasurable (B₂ * B₁) ?_
    filter_upwards [hae] with p hp
    exact hbound p.1 p.2.2 _ ⟨p.2.1, subset_closure hp, rfl⟩
  have hL : ∀ g : G1 ℚ, f.1 (gl g) * f0 W N ph φ.1 g =
      ∫ u in normOneFundamentalDomain E, ∫ h in N.D, H g u h ∂N.μ ∂normOneMeasure E := by
    intro g
    simp only [f0, J1, UI, mean, H]
    rw [← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun u => ?_)
    exact (integral_const_mul _ _).symm
  have hR : (J1 D N fun x => lift W M f.1 ph x * φ.1 x) =
      ∫ u in normOneFundamentalDomain E, ∫ h in N.D, ∫ g in M.D, H g u h ∂M.μ ∂N.μ ∂normOneMeasure E := by
    simp only [J1, UI, mean]
    refine integral_congr_ae (ae_of_all _ fun u => integral_congr_ae (ae_of_all _ fun h => ?_))
    simp only [lift, H]
    rw [← integral_mul_const]
    refine integral_congr_ae (ae_of_all _ fun g => ?_)
    simp only [hnux, dM_one', mul_one, mul_assoc]
  simp only [hL]
  rw [hR]
  exact swap3 _ _ _ H hInt
