import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisAtMinusRho
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoreConcl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGoodPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShellInt
import GroundTheory.GlobalFields.LocalAtPlace
open scoped TensorProduct NNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.EisRes
open GlobalTheory.Doubling (absE)
open GlobalTheory.PoleFactor

namespace GlobalTheory.NormFvFacts

theorem absNorm_gt_one (F : Type) [Field F] [NumberField F] (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) :
    1 < (Ideal.absNorm v.asIdeal : ℝ) := by
  have h1 : Ideal.absNorm v.asIdeal ≠ 1 := fun h => v.isPrime.ne_top (Ideal.absNorm_eq_one_iff.1 h)
  have h0 : Ideal.absNorm v.asIdeal ≠ 0 := fun h => v.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
  exact_mod_cast (by omega : 1 < Ideal.absNorm v.asIdeal)

theorem norm_eq_zpow (F : Type) [Field F] [NumberField F] (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F))
    (x : Fv F v) (hx : x ≠ 0) : ∃ k : ℤ, ‖x‖ = (Ideal.absNorm v.asIdeal : ℝ) ^ k := by
  have hv : Valued.v x ≠ 0 := (Valuation.ne_zero_iff _).2 hx
  refine ⟨Multiplicative.toAdd (WithZero.unzero hv), ?_⟩
  rw [FinitePlace.norm_def, WithZeroMulInt.toNNReal_neg_apply _ hv, NNReal.coe_zpow]
  rfl

theorem norm_le_one_iff (F : Type) [Field F] [NumberField F] (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F))
    (x : Fv F v) : ‖x‖ ≤ 1 ↔ x ∈ v.adicCompletionIntegers F := by
  rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers]
  exact Valued.toNormedField.norm_le_one_iff

theorem exists_norm_eq_inv (F : Type) [Field F] [NumberField F] (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) :
    ∃ ϖ : Fv F v, ‖ϖ‖ = (Ideal.absNorm v.asIdeal : ℝ)⁻¹ := by
  obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer F
  have h : Valued.v ((π : F) : v.adicCompletion F) = WithZero.exp (-1) := by
    rw [v.valuedAdicCompletion_eq_valuation']; exact hπ
  refine ⟨((π : F) : v.adicCompletion F), ?_⟩
  rw [FinitePlace.norm_def, h, WithZeroMulInt.toNNReal_neg_apply _ WithZero.exp_ne_zero, NNReal.coe_zpow]
  have key : ∀ (a : ℤ) (h : WithZero.exp a ≠ 0), Multiplicative.toAdd (WithZero.unzero h) = a := fun a h => rfl
  rw [key, zpow_neg_one]
  rfl

theorem sigmaFinite_haar (F : Type) [Field F] [NumberField F] (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F))
    (μ : Measure (Fv F v)) (hμ : μ.IsAddHaarMeasure) : SigmaFinite μ := by
  have : Countable F := (Module.finBasis ℚ F).equivFun.injective.countable
  have : TopologicalSpace.SeparableSpace (Fv F v) :=
    ⟨⟨Set.range (algebraMap F (Fv F v)), Set.countable_range _,
      IsDedekindDomain.HeightOneSpectrum.denseRange_algebraMap F v⟩⟩
  have : SecondCountableTopology (Fv F v) := UniformSpace.secondCountable_of_separable (Fv F v)
  have : LocallyCompactSpace (Fv F v) := inferInstance
  infer_instance

end GlobalTheory.NormFvFacts

open GlobalTheory.NormFvFacts in

theorem GlobalTheory.NormFvFacts.main : ∀ (F : Type) [Field F] [NumberField F] (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)), 1 < (Ideal.absNorm v.asIdeal : ℝ) ∧ (∀ x : Fv F v, x ≠ 0 → ∃ k : ℤ, ‖x‖ = (Ideal.absNorm v.asIdeal : ℝ) ^ k) ∧ (∀ x : Fv F v, ‖x‖ ≤ 1 ↔ x ∈ v.adicCompletionIntegers F) ∧ (∃ ϖ : Fv F v, ‖ϖ‖ = (Ideal.absNorm v.asIdeal : ℝ)⁻¹) ∧ ∀ μ : Measure (Fv F v), μ.IsAddHaarMeasure → SigmaFinite μ :=
  fun F _ _ v => ⟨absNorm_gt_one F v, norm_eq_zpow F v, norm_le_one_iff F v, exists_norm_eq_inv F v,
    fun μ hμ => sigmaFinite_haar F v μ hμ⟩
