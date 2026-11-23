import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.CharacterNorms.Aa
import Development.AutomorphicArithmetic.WhittakerHecke.MeasurePreservingIdeleScaleAndConjOnMaximalCompa
import Development.AutomorphicArithmetic.WhittakerHecke.RealIdeleMulAbsContinuousAndUnitAbsEqOne
import Development.AutomorphicArithmetic.WhittakerHecke.SchwartzBruhatRowLintegralAbsPowBounded
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical ENNReal NNReal
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)

private theorem row_nU (b : A ℚ) (g : G1 ℚ) (u : (A ℚ)ˣ) (j : Fin 2) :
    (gl (nU b * g) * dM u).val 1 j = (gl g * dM u).val 1 j := by
  rw [Units.val_mul, Units.val_mul, M.val_gl, M.val_gl, M.val_mul]
  simp [nU, Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct]

private theorem row_mD (a u : (A ℚ)ˣ) (k : G1 ℚ) (j : Fin 2) :
    (gl (mD a * cD u k) * dM u).val 1 j = ((a⁻¹ * u : (A ℚ)ˣ) : A ℚ) * G.row k j := by
  have h : gl (mD a * cD u k) = gl (mD a) * gl (cD u k) := map_mul _ _ _
  rw [h, mul_assoc, M.gl_cD, Units.val_mul, Units.val_mul, M.val_gl, M.val_gl]
  simp [mD, dM, G.row, Matrix.mul_apply, Fin.sum_univ_two, mul_assoc, Matrix.vecMul, dotProduct]

theorem UpperTheory.maximalCompact_integral_unipotent_norm_finite :
    ∀ (E : Type) [Field E] [NumberField E] (D : Dat ℚ E) (ω : HChar ℚ) (φ : GL (Fin 2) (A E) → ℂ), admitted D ω φ → ∀ (M₀ : Meas ℚ), ∀ Φ ∈ schwartzBruhatPi ℚ (Fin 2), ∀ (t : ℝ) (u : IdeleGroup ℚ), u ∈ UU →
        (_root_.UpperTheory.ConvolutionTheory.R2.M.J0 M₀ fun g => ∫⁻ b in fundamentalSet ℚ, ‖Un.Uu φ Φ t u (nU b * g)‖ₑ ∂(adeleMeasure ℚ)) ≠ ⊤ := by
  intro E _ _ D ω φ hA M₀ Φ hΦ t u hu
  obtain ⟨B, hB⟩ := hA.bdd
  obtain ⟨hmp, hme⟩ := UpperTheory.measurePreserving_idele_scale_and_conj_on_maximalCompact M₀ t u hu
  obtain ⟨C, hC⟩ := UpperTheory.schwartzBruhat_row_lintegral_abs_pow_bounded Φ hΦ 2 (by norm_num)
  obtain ⟨-, hiy, -, hU⟩ := UpperTheory.realIdele_mul_abs_continuous_and_unit_abs_eq_one
  haveI := M₀.prob
  have hw : ∀ g : G1 ℚ, ∫⁻ b in fundamentalSet ℚ, ‖Un.Uu φ Φ t u (nU b * g)‖ₑ ∂(adeleMeasure ℚ) ≤
      ENNReal.ofReal B * ‖Φ fun j => (iy (Real.exp t) : A ℚ) * (gl g * dM u).val 1 j‖ₑ := by
    intro g
    refine (lintegral_mono (g := fun _ => ENNReal.ofReal B * ‖Φ fun j => (iy (Real.exp t) : A ℚ) * (gl g * dM u).val 1 j‖ₑ)
      fun b => ?_).trans ?_
    · simp only [Un.Uu, row_nU, enorm_mul]
      refine mul_le_mul_left ?_ _
      rw [← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal (hB _)
    · rw [setLIntegral_const, adeleMeasure_fundamentalSet, mul_one]
  let F : IdeleGroup ℚ × G1 ℚ → ℝ≥0∞ := fun p =>
    ‖Φ fun j => ((p.1 : (A ℚ)ˣ) : A ℚ) * G.row p.2 j‖ₑ * ENNReal.ofReal (ab p.1 ^ (2 : ℝ))
  have hF : Measurable F := by
    have h1 : Continuous fun p : IdeleGroup ℚ × G1 ℚ => Φ fun j => ((p.1 : (A ℚ)ˣ) : A ℚ) * G.row p.2 j :=
      (continuous_of_mem_schwartzBruhatPi hΦ).comp (continuous_pi fun j =>
        (Units.continuous_val.comp continuous_fst).mul ((M.continuous_entry 1 j).comp continuous_snd))
    have h2 : Continuous fun p : IdeleGroup ℚ × G1 ℚ => ab p.1 ^ (2 : ℝ) :=
      (M.continuous_ab.comp continuous_fst).rpow_const fun _ => Or.inr (by norm_num)
    exact h1.measurable.enorm.mul h2.measurable.ennreal_ofReal
  have hI : ∫⁻ p, F p ∂M₀.ν ≤ C := by
    rw [Meas.ν, lintegral_prod_symm _ hF.aemeasurable]
    have hae : ∀ᵐ k ∂M₀.κ, k ∈ KK ℚ := by
      rw [ae_iff]
      exact M₀.supp
    refine (lintegral_mono_ae (g := fun _ => (C : ℝ≥0∞)) (hae.mono fun k hk => hC k hk)).trans ?_
    rw [lintegral_const, measure_univ, mul_one]
  unfold M.J0
  rw [← hmp.lintegral_comp_emb hme]
  have hK : ENNReal.ofReal B * ENNReal.ofReal ((Real.exp t)⁻¹ ^ 2) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  refine ne_top_of_le_ne_top (ENNReal.mul_ne_top hK (ENNReal.coe_ne_top (r := C))) ?_
  refine le_trans ?_ (mul_le_mul_right hI _)
  rw [← lintegral_const_mul _ hF]
  refine lintegral_mono fun p => ?_
  refine (mul_le_mul_right (hw _) _).trans (le_of_eq ?_)
  have e1 : (fun j => (iy (Real.exp t) : A ℚ) * (gl (mD (Un.aa t u p.1) * cD u p.2) * dM u).val 1 j) =
      fun j => ((p.1 : (A ℚ)ˣ) : A ℚ) * G.row p.2 j := by
    funext j
    rw [row_mD, ← mul_assoc, ← Units.val_mul]
    have : (iy (Real.exp t) * ((Un.aa t u p.1)⁻¹ * u) : (A ℚ)ˣ) = p.1 := by
      have h : ∀ x y z : (A ℚ)ˣ, x * ((x * y * z⁻¹)⁻¹ * y) = z := fun x y z => by
        rw [mul_left_comm, ← mul_assoc, mul_right_comm, mul_comm x y, mul_assoc _ y x, mul_comm y x, mul_inv, inv_inv,
          mul_right_comm, inv_mul_cancel, one_mul]
      exact h _ _ _
    rw [this]
  have e2 : M.wt (Un.aa t u p.1) = ENNReal.ofReal ((Real.exp t)⁻¹ ^ 2) * ENNReal.ofReal (ab p.1 ^ (2 : ℝ)) := by
    have h : ab (Un.aa t u p.1) = Real.exp t * (ab p.1)⁻¹ := by
      have h0 : ab (Un.aa t u p.1) = ab (iy (Real.exp t)) * ab u * ab (p.1⁻¹ : (A ℚ)ˣ) := by
        rw [← M.ab_mul, ← M.ab_mul]
        rfl
      rw [h0, hiy _ (Real.exp_ne_zero t), hU u hu, M.ab_inv, abs_of_pos (Real.exp_pos t), mul_one]
    rw [M.wt, h, ← ENNReal.ofReal_mul (by positivity), Real.rpow_two, mul_inv, inv_inv, mul_pow]
  simp only [e1, e2, F]
  ring
