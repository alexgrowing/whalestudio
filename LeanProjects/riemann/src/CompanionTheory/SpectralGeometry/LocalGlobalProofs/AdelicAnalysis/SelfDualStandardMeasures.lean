import Mathlib
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
import GroundTheory.GlobalFields.TateThesis.RootNumberLocalPlace
import GroundTheory.LocalFields.LocalFourier
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LocalFieldSelfdualMeasureExistsStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.DiscriminantDifferentProductFormulaStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ArchimedeanSelfdualMeasureDiscriminantScaledStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.SDOne
open GroundTheory.Global GroundTheory.LocalField

variable (F : Type) [Field F] [NumberField F]

theorem psiV_std (v : HeightOneSpectrum (𝓞 F)) (y : Fv F v) :
    psiV F (Circle.coeHom.compAddChar (adelicChar F)) v y = ((localAdelicChar F v y : Circle) : ℂ) := by
  classical
  show ((adelicChar F (pairA F 0 (singleV F v y)) : Circle) : ℂ) = ((adelicChar F (finitePlaceIncl v y) : Circle) : ℂ)
  congr 2

theorem coe_integers_eq (v : HeightOneSpectrum (𝓞 F)) :
    ((ValuativeRel.valuation (Fv F v)).integer : Set (Fv F v)) = (v.adicCompletionIntegers F : Set (Fv F v)) := by
  rw [show ((ValuativeRel.valuation (Fv F v)).integer : Set (Fv F v)) = (valBall (Fv F v) 0 : Set (Fv F v)) from coe_valBall_zero.symm]
  ext x
  show x ∈ valBall (Fv F v) 0 ↔ x ∈ v.adicCompletionIntegers F
  rw [mem_valBall_iff_valued, HeightOneSpectrum.mem_adicCompletionIntegers]
  simp

noncomputable def cV (v : HeightOneSpectrum (𝓞 F)) : ℝ≥0 :=
  (Ideal.absNorm v.asIdeal : ℝ≥0) ^ (((-differentExp v : ℤ) : ℝ) / 2)

theorem smul_eq_selfDualMeasure (v : HeightOneSpectrum (𝓞 F)) (lam : Measure (Fv F v)) (h : IsStdV v lam) :
    cV F v • lam = GroundTheory.LocalField.selfDualMeasure (localAdelicChar F v) := by
  obtain ⟨hH, h1⟩ := h
  have e := eq_smul_haarIntegers lam
  rw [coe_integers_eq F v, h1, one_smul] at e
  rw [e, GroundTheory.LocalField.selfDualMeasure, addCharConductor_localAdelicChar, residueCard_adicCompletion]
  rfl

theorem selfDual_std : ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F → ∀ (laminf : Measure (Ainf F)) (lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v)), IsStdInf laminf → (∀ v, IsStdV v (lam v)) → ∃ ψ, IsCharAF F ψ ∧ ∃ (cinf : ℝ≥0) (c : HeightOneSpectrum (𝓞 F) → ℝ≥0), IsUnitProd cinf c ∧ (SelfDual (cinf • laminf) (fun s t => psiInf F ψ (s * t))) ∧ ∀ v : HeightOneSpectrum (𝓞 F), (SelfDual (c v • lam v) (fun s t => psiV F ψ v (s * t))) := by
  intro F _ _ hF laminf lam hinf hlam
  refine ⟨Circle.coeHom.compAddChar (adelicChar F), ?_, Real.toNNReal (Real.sqrt |(discr F : ℝ)|), cV F, ?_, GlobalTheory.T.archimedean_selfdual_measure_discriminant_scaled F hF laminf hinf, fun v => ?_⟩
  · refine ⟨continuous_subtype_val.comp (continuous_adelicChar (K := F)), fun x => Circle.norm_coe _, fun a => ?_, ?_⟩
    · show ((adelicChar F _ : Circle) : ℂ) = 1
      rw [adelicChar_algebraMap]
      rfl
    · by_contra h
      push Not at h
      apply adelicChar_ne_one (K := F)
      ext x
      exact h x
  · exact GlobalTheory.T.discriminant_different_product_formula F
  · rw [smul_eq_selfDualMeasure F v (lam v) (hlam v)]
    simp only [psiV_std]
    exact GlobalTheory.T.local_field_selfdual_measure_exists _ _ (continuous_localAdelicChar v) (localAdelicChar_ne_one v)

end GlobalTheory.CompanionTheory.SW.SDOne
