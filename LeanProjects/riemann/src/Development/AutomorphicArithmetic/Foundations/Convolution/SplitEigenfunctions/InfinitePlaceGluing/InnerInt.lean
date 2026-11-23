import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.Entire
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.VolD
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.ContinuousEntry
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnitaryActions.ContinuousAdelicGL2OfContinuousEntries
import GroundTheory.AutomorphicForms.CompactFormulaCountable

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2
open scoped Classical

namespace UpperTheory.ConvolutionTheory.RankTwoDescent

variable {E : Type} [Field E] [NumberField E]

private theorem cont_em : Continuous (em E) := by
  have hM : Continuous ((AdeleBaseChange.adeleMap ℚ E).mapMatrix.toMonoidHom :
      Matrix (Fin 2) (Fin 2) (A ℚ) → Matrix (Fin 2) (Fin 2) (A E)) :=
    continuous_id.matrix_map AdeleBaseChange.continuous_adeleMap
  exact Continuous.units_map _ hM

private theorem sc_idele : SecondCountableTopology (IdeleGroup ℚ) := by
  haveI : SecondCountableTopology (A ℚ) := GroundTheory.Automorphic.secondCountableTopology_adeleRing ℚ
  haveI : SecondCountableTopology (A ℚ)ᵐᵒᵖ := MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  exact Units.isEmbedding_embedProduct.secondCountableTopology

private theorem cont_in {φ : GL (Fin 2) (A E) → ℂ} (hc : Continuous φ) (t : (A ℚ)ˣ) :
    Continuous fun g : G1 ℚ => φ (em E (gl g * dM t)) :=
  hc.comp (cont_em.comp (Matrix.SpecialLinearGroup.continuous_toGL.mul continuous_const))

private theorem inner_int (M : Meas ℚ) {φ : GL (Fin 2) (A E) → ℂ} (hc : Continuous φ) {B : ℝ}
    (hB : ∀ g, ‖φ g‖ ≤ B) (t : (A ℚ)ˣ) :
    IntegrableOn (fun g : G1 ℚ => φ (em E (gl g * dM t))) M.D M.μ := by
  haveI : IsFiniteMeasure (M.μ.restrict M.D) := ⟨by simpa using UpperTheory.ConvolutionTheory.R2.M.volD ℚ M⟩
  exact Integrable.of_bound (cont_in hc t).aestronglyMeasurable B (ae_of_all _ fun g => hB _)

private theorem outer_int (M : Meas ℚ) (U : UMeas) (χ : HChar ℚ) (hχ : ∀ a, ‖((χ.1 a : ℂˣ) : ℂ)‖ = 1)
    {φ : GL (Fin 2) (A E) → ℂ} (hc : Continuous φ) {B : ℝ} (hB : ∀ g, ‖φ g‖ ≤ B) :
    Integrable (fun t => ((χ.1 t : ℂˣ) : ℂ) * ∫ g in M.D, φ (em E (gl g * dM t)) ∂M.μ) U.υ := by
  haveI := U.prob
  haveI : IsFiniteMeasure (M.μ.restrict M.D) := ⟨by simpa using UpperTheory.ConvolutionTheory.R2.M.volD ℚ M⟩
  haveI := sc_idele
  have hF : Continuous fun t : IdeleGroup ℚ => ∫ g in M.D, φ (em E (gl g * dM t)) ∂M.μ := by
    refine continuous_of_dominated (bound := fun _ => B) ?_ ?_ (integrable_const B) ?_
    · exact fun t => (cont_in hc t).aestronglyMeasurable
    · exact fun t => ae_of_all _ fun g => hB _
    · exact ae_of_all _ fun g =>
        hc.comp (cont_em.comp (continuous_const.mul UpperTheory.ConvolutionTheory.R2.continuous_dM))
  have hχc : Continuous fun t : IdeleGroup ℚ => ((χ.1 t : ℂˣ) : ℂ) :=
    Units.continuous_val.comp χ.2.1
  refine Integrable.of_bound (hχc.mul hF).aestronglyMeasurable (B * (M.μ.restrict M.D).real Set.univ)
    (ae_of_all _ fun t => ?_)
  rw [norm_mul, hχ, one_mul]
  exact norm_integral_le_of_norm_le_const (ae_of_all _ fun g => hB _)

private theorem per_add (M : Meas ℚ) (U : UMeas) (χ : HChar ℚ) (hχ : ∀ a, ‖((χ.1 a : ℂˣ) : ℂ)‖ = 1)
    {φ₁ φ₂ : GL (Fin 2) (A E) → ℂ} (h₁ : Continuous φ₁) (h₂ : Continuous φ₂) {B₁ B₂ : ℝ}
    (b₁ : ∀ g, ‖φ₁ g‖ ≤ B₁) (b₂ : ∀ g, ‖φ₂ g‖ ≤ B₂) :
    Per M U χ (φ₁ + φ₂) = Per M U χ φ₁ + Per M U χ φ₂ := by
  unfold Per
  rw [← integral_add (outer_int M U χ hχ h₁ b₁) (outer_int M U χ hχ h₂ b₂)]
  refine integral_congr_ae (ae_of_all _ fun t => ?_)
  simp only [Pi.add_apply]
  rw [integral_add (inner_int M h₁ b₁ t) (inner_int M h₂ b₂ t), mul_add]

private theorem per_smul (M : Meas ℚ) (U : UMeas) (χ : HChar ℚ) (c : ℂ) (φ : GL (Fin 2) (A E) → ℂ) :
    Per M U χ (c • φ) = c * Per M U χ φ := by
  unfold Per
  rw [← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun t => ?_)
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [integral_const_mul]
  ring

private theorem per_zero (M : Meas ℚ) (U : UMeas) (χ : HChar ℚ) :
    Per M U χ (0 : GL (Fin 2) (A E) → ℂ) = 0 := by
  simp [Per]

end UpperTheory.ConvolutionTheory.RankTwoDescent

open UpperTheory.ConvolutionTheory.RankTwoDescent

theorem UpperTheory.ConvolutionTheory.RankTwoDescent.perTr_of :
    PerTr := by
  intro E _ _ _ D P ω χ _ hω hχω hAdm M U hNo φ hφ
  have hχ : ∀ a, ‖((χ.1 a : ℂˣ) : ℂ)‖ = 1 := by
    intro a
    have h := congrArg (fun u : ℂˣ => ‖(u : ℂ)‖) (hχω a)
    simp only [Units.val_pow_eq_pow_val, Units.val_mul, norm_pow, norm_mul, hω a, mul_one,
      Units.val_one, norm_one] at h
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h
  induction hφ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, hf, h, rfl⟩ := hx
    exact hNo f hf h
  | zero => exact per_zero M U χ
  | add x y hx hy ihx ihy =>
    obtain ⟨B₁, b₁⟩ := (hAdm x hx).bdd
    obtain ⟨B₂, b₂⟩ := (hAdm y hy).bdd
    rw [per_add M U χ hχ (hAdm x hx).cont (hAdm y hy).cont b₁ b₂, ihx, ihy, add_zero]
  | smul c x hx ih =>
    rw [per_smul, ih, mul_zero]

end
