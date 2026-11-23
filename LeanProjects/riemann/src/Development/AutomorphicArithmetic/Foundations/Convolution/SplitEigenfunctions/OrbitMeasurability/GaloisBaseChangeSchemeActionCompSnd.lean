import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.OrbitMeasurability.PerCont
import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.OrbitMeasurability.AbsUnf
import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.OrbitMeasurability.QuadraticFormRationalPoints
import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.OrbitMeasurability.BddE
import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.SzLaws
import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.DiagInvVal
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.CdMeas
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.VolD
import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.UnitsCpt
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnitaryActions.ContinuousAdelicGL2OfContinuousEntries
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnitaryActions.ContinuousQuaternaryQuadraticForm

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff UpperTheory.ConvolutionTheory.RankTwoDescent UpperTheory.ConvolutionTheory.RankTwoDescent.Cp
open scoped Classical ENNReal

namespace UpperTheory.ConvolutionTheory.RankTwoDescent.Cp

private noncomputable def hoD {F : Type} [Field F] [NumberField F] (t : (A F)ˣ) : G1 F ≃ₜ G1 F :=
  ⟨⟨cD t, cD t⁻¹, fun g => by rw [← cD_mul_left, inv_mul_cancel, cD_one_left],
      fun g => by rw [← cD_mul_left, mul_inv_cancel, cD_one_left]⟩,
    M.continuous_cD t, M.continuous_cD t⁻¹⟩

private theorem emb_cD {F : Type} [Field F] [NumberField F] (t : (A F)ˣ) : MeasurableEmbedding (cD t : G1 F → G1 F) :=
  (hoD t).measurableEmbedding

private noncomputable def tau {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] (z : (A E)ˣ) : (A E)ˣ :=
  Units.map ((am E : A ℚ →+* A E) : A ℚ →* A E) (ideleNorm ℚ E z)

private theorem em_dM {E : Type} [Field E] [NumberField E] (t : (A ℚ)ˣ) :
    em E (dM t) = dM (Units.map ((am E : A ℚ →+* A E) : A ℚ →* A E) t) := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [em, dM, Matrix.GeneralLinearGroup.map]

private theorem gl_scalarCenter_commute {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] (D : Dat ℚ E) (z : (A E)ˣ) (u : G1 E) :
    gl u * sZ D z = sZ D z * gl (cD (tau z) u) := by
  obtain ⟨-, -, -, -, -, -, -, -, hsc, -, -⟩ := UpperTheory.ConvolutionTheory.RankTwoDescent.szLaws E D
  have e : em E (dM (ideleNorm ℚ E z)⁻¹) = (dM (tau z))⁻¹ := by
    rw [em_dM, map_inv, dM_inv]; rfl
  rw [hsc, e, gl_cD]
  rw [← mul_assoc, ← UpperTheory.ConvolutionTheory.R2.scalar_comm z (gl u)]
  group

private theorem cD_j {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] (D : Dat ℚ E) (z : (A E)ˣ)
    (j : G1 ℚ →* G1 E) (hj : ∀ g, gl (j g) = em E (gl g)) (g : G1 ℚ) :
    cD (tau z) (j (cD (ideleNorm ℚ E z)⁻¹ g)) = j g := by
  obtain ⟨-, -, -, -, -, -, -, hc, -, -, -⟩ := UpperTheory.ConvolutionTheory.RankTwoDescent.szLaws E D
  apply gl_injective
  have h1 := gl_scalarCenter_commute D z (j (cD (ideleNorm ℚ E z)⁻¹ g))
  rw [hj, ← hc, ← hj] at h1
  exact (mul_left_cancel h1).symm

private theorem galoisBaseChangeSchemeAction_comp_snd {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] (D : Dat ℚ E) (z : (A E)ˣ) (h u r : G1 E)
    (huh : h = r * u) :
    D.act (gl h * sZ D z)⁻¹ (D.act (gl r) (rp X0)) = D.act (gl (cD (tau z) u))⁻¹ (rp X0) := by
  obtain ⟨-, -, -, -, ha, -, -, -, -, -, -⟩ := UpperTheory.ConvolutionTheory.RankTwoDescent.szLaws E D
  have h0 : D.act (sZ D z)⁻¹ (rp X0) = rp X0 := by
    conv_lhs => rw [← ha z]
    exact D.act_inv_act _ _
  subst huh
  rw [← D.act_mul, gl_mul, mul_assoc, gl_scalarCenter_commute D z u]
  have : (gl r * (sZ D z * gl (cD (tau z) u)))⁻¹ * gl r = (gl (cD (tau z) u))⁻¹ * (sZ D z)⁻¹ := by group
  rw [this, D.act_mul, h0]

private theorem pY_eq {E : Type} [Field E] [NumberField E] (D : Dat ℚ E) (z : ↥(IdeleGroup.normOneSubgroup E)) (p : G1 E × Orb D.δ) :
    pY D (z, p) = D.act (gl p.1 * sZ D (z : IdeleGroup E))⁻¹ (rp p.2.1) := rfl

private theorem el_eq {E : Type} [Field E] [NumberField E] (D : Dat ℚ E) (z : ↥(IdeleGroup.normOneSubgroup E)) (p : G1 E × Orb D.δ) :
    el D (z, p) = gl p.1 * sZ D (z : IdeleGroup E) := rfl

end UpperTheory.ConvolutionTheory.RankTwoDescent.Cp

theorem UpperTheory.ConvolutionTheory.RankTwoDescent.Cp.zOne :
    UpperTheory.ConvolutionTheory.RankTwoDescent.Cp.ZOne := by
  intro E _ _ _ D W M N P φ hφ j hj c hc hcs Ψ hΨ z
  obtain ⟨j', r, hj', hjc, hji, hr, hjΓ, hu⟩ := UpperTheory.ConvolutionTheory.RankTwoDescent.Cp.reps E D
  have hjj : j' = j := MonoidHom.ext fun g => gl_injective ((hj' g).trans (hj g).symm)
  subst hjj
  haveI := N.haar
  haveI := N.right
  haveI := M.haar
  haveI := M.right
  haveI : DiscreteMeasurableSpace (Orb D.δ) := ⟨fun _ => trivial⟩
  haveI : Countable (Orb D.δ) := inferInstance
  obtain ⟨hcont, hleft⟩ := (UpperTheory.ConvolutionTheory.RankTwoDescent.decE E P φ hφ).1
  simp only [pY_eq, el_eq]
  generalize ((z : IdeleGroup E) : (A E)ˣ) = zz
  have hmpE : MeasurePreserving (cD (tau zz)) N.μ N.μ := (UpperTheory.ConvolutionTheory.RankTwoDescent.invE E N).1 _
  have hmpQ : MeasurePreserving (cD (ideleNorm ℚ E zz)⁻¹ : G1 ℚ → G1 ℚ) M.μ M.μ := UpperTheory.ConvolutionTheory.R2.M.cdMeas ℚ M _
  have hq : ∀ F : G1 ℚ → ℂ, ∫ g, F (cD (ideleNorm ℚ E zz)⁻¹ g) ∂M.μ = ∫ g, F g ∂M.μ :=
    fun F => hmpQ.integral_comp (emb_cD _) F
  obtain ⟨cs, hcsd⟩ : ∃ cs : G1 E → ℂ, ∀ y, cs y = c (cD (tau zz) y) := ⟨_, fun _ => rfl⟩
  obtain ⟨f, hfd⟩ : ∃ f : G1 E → ℂ, ∀ x, f x = φ.1 (gl x * sZ D zz) := ⟨_, fun _ => rfl⟩
  have hcsC : Continuous cs := by
    rw [show cs = c ∘ cD (tau zz) from funext hcsd]
    exact hc.comp (UpperTheory.ConvolutionTheory.R2.M.continuous_cD _)
  have hfC : Continuous f := by
    rw [show f = fun x => φ.1 (gl x * sZ D zz) from funext hfd]
    exact hcont.comp (continuous_gl.mul continuous_const)
  have hcsS : HasCompactSupport cs := by
    rw [show cs = c ∘ hoD (tau zz) from funext hcsd]
    exact hcs.comp_homeomorph _
  have hΨ' : ∀ (h : G1 E) (ξ : Orb D.δ), Ψ (D.act (gl h * sZ D zz)⁻¹ (rp ξ.1)) = ∫ g, cs (j' g * ((r ξ)⁻¹ * h)) ∂M.μ := by
    intro h ξ
    have e1 : D.act (gl h * sZ D zz)⁻¹ (rp ξ.1) = D.act (gl (cD (tau zz) ((r ξ)⁻¹ * h)))⁻¹ (rp X0) := by
      rw [(hr ξ).2]
      exact galoisBaseChangeSchemeAction_comp_snd D zz h _ (r ξ) (by group)
    rw [e1, hΨ, ← hq fun g => cs (j' g * ((r ξ)⁻¹ * h))]
    refine integral_congr_ae (ae_of_all _ fun g => ?_)
    simp only [hcsd]
    rw [UpperTheory.ConvolutionTheory.R2.cD_mul _ (j' _) _, cD_j D zz j' hj' g]
  have hB : ∃ B : ℝ, ∀ x, ‖f x‖ ≤ B := by
    obtain ⟨B, hB⟩ := UpperTheory.ConvolutionTheory.RankTwoDescent.Cp.bddE E P φ hφ {sZ D zz} isCompact_singleton
    exact ⟨B, fun x => by rw [hfd]; exact hB x _ rfl⟩
  have hinv : ∀ γ ∈ Gam E, ∀ x, f (γ * x) = f x := by
    rintro _ ⟨γ, rfl⟩ x
    rw [hfd, hfd, gl_mul, gl_ratS, mul_assoc, hleft]
  obtain ⟨h1, h2⟩ := UpperTheory.ConvolutionTheory.RankTwoDescent.Cp.absUnf (G1 E) (G1 ℚ) (Orb D.δ) N.μ M.μ j' (Gam E) (Gam ℚ) N.D M.D r f cs hjc hji N.fund M.fund
    (UpperTheory.ConvolutionTheory.R2.M.volD ℚ M) (fun i => (hr i).1) hjΓ hu hfC.measurable hinv hB hcsC.measurable (hcsC.integrable_of_hasCompactSupport hcsS)
  have hL : ∀ p : G1 E × Orb D.δ, Ψ (D.act (gl p.1 * sZ D zz)⁻¹ (rp p.2.1)) * φ.1 (gl p.1 * sZ D zz) =
      (∫ g, cs (j' g * ((r p.2)⁻¹ * p.1)) ∂M.μ) * f p.1 := by
    rintro ⟨h, ξ⟩
    rw [hΨ', hfd]
  refine ⟨fun B hBB => ?_, ?_⟩
  · simp only [hL]
    refine (h1 B (fun h => by rw [hfd]; exact hBB h)).trans_eq ?_
    rw [show (∫⁻ y, ‖cs y‖ₑ ∂N.μ) = ∫⁻ y, ‖c y‖ₑ ∂N.μ by
      simp only [hcsd]; exact hmpE.lintegral_comp_emb (emb_cD _) fun y => ‖c y‖ₑ]
  · simp only [hL]
    rw [h2]
    have := hmpE.integral_comp (emb_cD (tau zz)) fun y => c y * SLP M fun x => φ.1 (x * sZ D zz * gl y)
    rw [← this]
    refine integral_congr_ae (ae_of_all _ fun y => ?_)
    simp only [hcsd, SLP]
    congr 1
    refine integral_congr_ae (ae_of_all _ fun g => ?_)
    simp only [hfd]
    rw [gl_mul, hj', mul_assoc, gl_scalarCenter_commute D zz y, mul_assoc]
