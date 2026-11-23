import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesCharacterSUTrivialTwo
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SquareIntegrableIffExtension
open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S GlobalTheory.OpTrace GlobalTheory.HCChar GlobalTheory.SUChar
open GlobalTheory.Orb (ujMat ujRep CcMat IsCharFn IsRegSS)
open GlobalTheory.DSSU (SUJ SUset Ext)
open GlobalTheory.SqIntSU (scalarMul circleHaar)

noncomputable section

namespace GlobalTheory.ScalarTwist

attribute [local instance] GlobalTheory.SqIntSU.circleBorelMS GlobalTheory.SqIntSU.circleBorelSpace GlobalTheory.SqIntSU.circleHaar_isHaar
  GlobalTheory.SqIntSU.circleHaar_finite GlobalTheory.SqIntSU.locallyCompact_special GlobalTheory.SqIntSU.secondCountable_special
  GlobalTheory.SqIntSU.sigmaCompact_special GlobalTheory.DSSU.borelSpace_SUJ

theorem ujMat_scalarMul {n : ℕ} (ε : Fin n → Bool) (z : Circle) (g : SUJ ε) :
    ujMat ε (scalarMul ε (z, g)) = (z : ℂ) • suMat ε g := by
  show umat (GlobalTheory.SqIntSU.unitScalar ε z) * umat (g : UJ ε) = _
  rw [GlobalTheory.SqIntSU.umat_unitScalar, Matrix.smul_mul, Matrix.one_mul]
  rfl

theorem scalar_twist : ∀ (n : ℕ), 1 ≤ n → ∀ (ε : Fin n → Bool) (μ : Measure (UJ ε)) [μ.IsHaarMeasure] (μ' : Measure (SUJ ε)) [μ'.IsHaarMeasure], ∃ c : NNReal, c ≠ 0 ∧ (letI := GlobalTheory.SqIntSU.circleBorelMS; μ = c • Measure.map (scalarMul ε) (circleHaar.prod μ')) ∧ ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V] (m : ℤ) (π' π : Matrix (Fin n) (Fin n) ℂ → (V →L[ℂ] V)) (h' : IsURepOn (SUset ε) π') (h : IsURepOn (UJset ε) π), Ext ε m π' π → ∀ f : UJ ε → ℂ, Continuous f → HasCompactSupport f → repOp (ujRep h) μ f = ((c : ℝ) : ℂ) • repOp (suRep h') μ' fun g : SUJ ε => ∫ z, f (scalarMul ε (z, g)) * (z : ℂ) ^ m ∂circleHaar := by
  intro n hn ε μ _ μ' _
  have hn0 : 0 < n := hn
  haveI : SFinite μ' := inferInstance
  haveI : (circleHaar.prod μ').IsHaarMeasure := Measure.prod.instIsHaarMeasure _ _
  have hsc : Continuous (scalarMul ε) := GlobalTheory.SqIntSU.continuous_scalarMul ε
  haveI hν : (Measure.map (scalarMul ε) (circleHaar.prod μ')).IsHaarMeasure :=
    Measure.isHaarMeasure_map _ (scalarMul ε) hsc (GlobalTheory.SqIntSU.scalarMul_surjective ε hn0)
      (GlobalTheory.SqIntSU.scalarMul_proper ε)
  set ν := Measure.map (scalarMul ε) (circleHaar.prod μ') with hνdef
  have hmu : μ = μ.haarScalarFactor ν • ν := Measure.isMulLeftInvariant_eq_smul μ ν
  have hc0 : μ.haarScalarFactor ν ≠ 0 := (Measure.haarScalarFactor_pos_of_isHaarMeasure μ ν).ne'
  refine ⟨μ.haarScalarFactor ν, hc0, hmu, ?_⟩
  intro V _ _ _ m π' π h' h hE f hf hfc
  set c := μ.haarScalarFactor ν
  have hUc : Continuous (ujMat ε) := Units.continuous_val.comp continuous_subtype_val
  have hU : IsUnitaryRep (ujRep h) := GlobalTheory.Orb.isUnitaryRep_repVia h (fun g => g.2) hUc
  have hpt : ∀ (z : Circle) (g : SUJ ε), ujRep h (scalarMul ε (z, g)) = (z : ℂ) ^ m • suRep h' g := by
    intro z g
    show π (ujMat ε (scalarMul ε (z, g))) = (z : ℂ) ^ m • π' (suMat ε g)
    rw [ujMat_scalarMul]
    exact hE z (Circle.norm_coe z) _ (suMat_mem ε g)
  set fm : SUJ ε → ℂ := fun g => ∫ z, f (scalarMul ε (z, g)) * (z : ℂ) ^ m ∂circleHaar with hfm
  have hR := hU.isRepOp (μ := μ) hf hfc
  have key : ∀ v, Integrable (fun g => fm g • suRep h' g v) μ' ∧
      ((c : ℂ)⁻¹ • repOp (ujRep h) μ f) v = ∫ g, fm g • suRep h' g v ∂μ' := by
    intro v
    set F : UJ ε → V := fun g => f g • ujRep h g v with hF
    have hFc : Continuous F := hf.smul (hU.continuous_apply v)
    have hFi : Integrable F ν := hFc.integrable_of_hasCompactSupport hfc.smul_right
    have hGi : Integrable (F ∘ scalarMul ε) (circleHaar.prod μ') :=
      (integrable_map_measure hFi.aestronglyMeasurable hsc.aemeasurable).1 hFi
    have hin : ∀ g : SUJ ε, ∫ z, (F ∘ scalarMul ε) (z, g) ∂circleHaar = fm g • suRep h' g v := by
      intro g
      have : ∀ z : Circle, (F ∘ scalarMul ε) (z, g) = (f (scalarMul ε (z, g)) * (z : ℂ) ^ m) • suRep h' g v := by
        intro z
        simp only [Function.comp, hF, hpt, ContinuousLinearMap.smul_apply, smul_smul]
      simp only [this]
      exact integral_smul_const _ _
    refine ⟨?_, ?_⟩
    · have := hGi.integral_prod_right
      simpa only [hin] using this
    · rw [ContinuousLinearMap.smul_apply, (hR v).2]
      conv_lhs => rw [hmu]
      rw [integral_smul_nnreal_measure, hνdef, integral_map hsc.aemeasurable
        (hFc.aestronglyMeasurable),
        show ∫ x, F (scalarMul ε x) ∂(circleHaar.prod μ') = ∫ g, ∫ z, (F ∘ scalarMul ε) (z, g) ∂circleHaar ∂μ' from
          integral_prod_symm _ hGi]
      simp only [hin]
      have : (c : ℂ) ≠ 0 := by exact_mod_cast hc0
      rw [NNReal.smul_def, ← Complex.coe_smul, smul_smul, inv_mul_cancel₀ this, one_smul]
  have hT : IsRepOp (suRep h') μ' fm ((c : ℂ)⁻¹ • repOp (ujRep h) μ f) := fun v => ⟨(key v).1, (key v).2⟩
  rw [hT.repOp_eq, smul_smul]
  have : (c : ℂ) ≠ 0 := by exact_mod_cast hc0
  simp [this]

end GlobalTheory.ScalarTwist
