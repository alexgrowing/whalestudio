import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.CharacterNorms.Aa
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.MeasMul
import Development.AutomorphicArithmetic.WhittakerHecke.MeasurePreservingIdeleScaleAndConjOnMaximalCompa
import Development.AutomorphicArithmetic.WhittakerHecke.MaximalCompactIntegralUnipotentNormFinite
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical ENNReal NNReal
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)

private theorem cont_em {E : Type} [Field E] [NumberField E] : Continuous (em E) :=
  Continuous.units_map _ (Continuous.matrix_map continuous_id AdeleBaseChange.continuous_adeleMap)

private theorem ex_rat {E : Type} [Field E] [NumberField E] (γ : Matrix.SpecialLinearGroup (Fin 2) ℚ) :
    ∃ γ', em E (gl (ratS ℚ γ)) = ratGL E 2 γ' := by
  refine ⟨Matrix.GeneralLinearGroup.map (algebraMap ℚ E) (Matrix.SpecialLinearGroup.toGL γ), ?_⟩
  apply Units.ext
  ext i j
  rw [ratGL_apply]
  exact AdeleBaseChange.adeleMap_algebraMap _

private theorem glm (g h : G1 ℚ) : gl (g * h) = gl g * gl h := map_mul _ _ _

private theorem row_nU (b : A ℚ) (h : GL (Fin 2) (A ℚ)) (j : Fin 2) : (gl (nU b) * h).val 1 j = h.val 1 j := by
  rw [Units.val_mul, M.val_gl]
  simp [nU, Matrix.mul_apply, Fin.sum_univ_two]

private theorem row_rat (γ : Matrix.SpecialLinearGroup (Fin 2) ℚ) (h : GL (Fin 2) (A ℚ)) (j : Fin 2) :
    (gl (ratS ℚ γ) * h).val 1 j = ((fun i => rt (γ.1 1 i)) ᵥ* h.val) j := by
  rw [Units.val_mul, M.val_gl, M.val_ratS]
  rfl

theorem UpperTheory.setIntegral_restrict_mul_thetaKernel_eq_unfolded :
    ∀ (E : Type) [Field E] [NumberField E] (D : Dat ℚ E) (ω : HChar ℚ) (φ : GL (Fin 2) (A E) → ℂ), admitted D ω φ → ∀ (M₀ : Meas ℚ), ∀ Φ ∈ schwartzBruhatPi ℚ (Fin 2), ∀ (t : ℝ) (u : IdeleGroup ℚ), u ∈ UU →
        ∫ g in M₀.D, φ (em E (gl g * dM u)) * ThR Φ t (gl g * dM u) ∂M₀.μ = ∫ p, Un.Tt φ Φ t u p ∂M₀.ν := by
  intro E _ _ D ω φ hA M₀ Φ hΦ t u hu
  obtain ⟨σ, hσ⟩ := G.exists_rowSec (F := ℚ)
  obtain ⟨hmp, hme⟩ := UpperTheory.measurePreserving_idele_scale_and_conj_on_maximalCompact M₀ t u hu
  have hleft : ∀ (γ : Matrix.SpecialLinearGroup (Fin 2) ℚ) (h : GL (Fin 2) (A ℚ)), φ (em E (gl (ratS ℚ γ) * h)) = φ (em E h) := by
    intro γ h
    obtain ⟨γ', e⟩ := ex_rat (E := E) γ
    rw [map_mul, e, hA.left]
  have hg : Continuous fun g : G1 ℚ => gl g * dM u := M.continuous_gl.mul continuous_const
  have hm : Measurable (Un.Uu φ Φ t u) := by
    refine Continuous.measurable ?_
    refine (hA.cont.comp (cont_em.comp hg)).mul ((continuous_of_mem_schwartzBruhatPi hΦ).comp (continuous_pi fun j => ?_))
    exact continuous_const.mul ((Units.continuous_val.comp hg).matrix_elem 1 j)
  have hinv : ∀ (ξ : ℚ) g, Un.Uu φ Φ t u (nU (rt ξ) * g) = Un.Uu φ Φ t u g := by
    intro ξ g
    have e : gl (nU (rt ξ) * g) * dM u = gl (nU (rt ξ)) * (gl g * dM u) := by rw [glm, mul_assoc]
    have e' : φ (em E (gl (nU (rt ξ)) * (gl g * dM u))) = φ (em E (gl g * dM u)) := by
      rw [← M.ratS_up]
      exact hleft _ _
    unfold Un.Uu
    rw [e, e']
    simp only [row_nU]
  have key := (M.unfC ℚ M₀ σ (Un.Uu φ Φ t u) hσ hm hinv (UpperTheory.maximalCompact_integral_unipotent_norm_finite E D ω φ hA M₀ Φ hΦ t u hu)).2.2.2
  have e1 : ∀ g, φ (em E (gl g * dM u)) * ThR Φ t (gl g * dM u) = ∑' r, Un.Uu φ Φ t u (ratS ℚ (σ r) * g) := by
    intro g
    unfold ThR
    rw [← tsum_mul_left]
    refine tsum_congr fun r => ?_
    have e : gl (ratS ℚ (σ r) * g) * dM u = gl (ratS ℚ (σ r)) * (gl g * dM u) := by rw [glm, mul_assoc]
    unfold Un.Uu
    rw [e, hleft]
    simp only [row_rat]
    rw [hσ r]
  simp only [e1]
  rw [key, Meas.I0, ← hmp.integral_comp hme]
  refine integral_congr_ae (Eventually.of_forall fun p => ?_)
  have e2 : ∀ b, gl (nU b * (mD (Un.aa t u p.1) * cD u p.2)) * dM u =
      gl (nU b) * (gl (mD (Un.aa t u p.1)) * dM u * gl p.2) := by
    intro b
    rw [glm, glm, mul_assoc, mul_assoc, M.gl_cD, mul_assoc]
  simp only [iw, Un.Tt, Un.Uu, Un.Fb, e2, row_nU]
  rw [integral_mul_const, ← mul_assoc]
  simp only [map_mul (em E) (gl (nU _))]
