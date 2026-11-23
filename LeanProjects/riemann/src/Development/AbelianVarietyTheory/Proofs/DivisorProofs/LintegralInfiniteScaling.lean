import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvIInfScaleMul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterInvariantAdelicFormEqMulEvalZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdelicSchwartzNeZeroAtOrigin
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergWordL2Bound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasurableThetaSumOfSchrodinger
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HaarModulusOfUnitCompletionsAtPlacesEqProdNorm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModulusOfNormEqAbs
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup
open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Classical

noncomputable section

namespace GlobalTheory.TorusTheta

variable (F : Type) [Field F] [NumberField F]

theorem infScale_mul' (a b : ℝ) : infScale F a * infScale F b = infScale F (a * b) := by
  refine Prod.ext ?_ ?_
  · show (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm _ * (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm _ = _
    rw [← map_mul, ← map_mul]
    rfl
  · show (1 : FiniteAdeleRing (𝓞 F) F) * 1 = 1
    exact mul_one 1

theorem infScale_one' : infScale F 1 = 1 := by
  simp only [infScale, map_one]
  rfl

theorem norm_infScale_fst (t : ℝ) (w : InfinitePlace F) : ‖(infScale F t).1 w‖ = |t| := by
  rw [← GroundTheory.Global.normAtPlace_homeomorphMixedSpace, GroundTheory.Global.homeomorphMixedSpace_apply]
  simp only [infScale, RingEquiv.apply_symm_apply]
  exact mixedEmbedding.normAtPlace_real w t

theorem distribHaarChar_infScale (t : ℝ) (ht : 0 < t) (a : (AF F)ˣ) (ha : (a : AF F) = infScale F t) :
    (distribHaarChar (AF F) a : ℝ) = t ^ Module.finrank ℚ F := by
  rw [GlobalTheory.ModuAdele.distribHaarChar_adeleRing, GroundTheory.Global.IdeleGroup.ideleModule_eq]
  have h2 : ∏ᶠ v : HeightOneSpectrum (𝓞 F), ‖((a : AdeleRing (𝓞 F) F)).2 v‖ = 1 := by
    refine finprod_eq_one_of_forall_eq_one fun v => ?_
    rw [show (a : AdeleRing (𝓞 F) F) = infScale F t from ha]
    simp [infScale]
  rw [h2, mul_one]
  simp_rw [show (a : AdeleRing (𝓞 F) F) = infScale F t from ha, norm_infScale_fst, abs_of_pos ht]
  rw [Finset.prod_pow_eq_pow_sum, InfinitePlace.sum_mult_eq]

theorem lintegral_infScale_pi : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (u : κ → ℝ), (∀ j, 0 < u j) →
    ∀ (μ : @Measure (κ → AF F) (borel _)), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
    ∀ (f : (κ → AF F) → ℝ≥0∞), ∫⁻ x, f (fun j => GlobalTheory.TorusTheta.infScale F (u j) * x j) ∂μ =
      (ENNReal.ofReal (∏ j, u j ^ Module.finrank ℚ F))⁻¹ * ∫⁻ x, f x ∂μ := by
  intro F _ _ κ _ u hu μ hμ f
  letI : MeasurableSpace (κ → AF F) := borel _
  haveI : BorelSpace (κ → AF F) := ⟨rfl⟩
  haveI : LocallyCompactSpace (AF F) := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele F
  haveI : SecondCountableTopology (AF F) := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  haveI := hμ
  let s : (κ → AF F)ˣ :=
    { val := fun j => infScale F (u j)
      inv := fun j => infScale F (u j)⁻¹
      val_inv := funext fun j => by
        show infScale F (u j) * infScale F (u j)⁻¹ = 1
        rw [infScale_mul', mul_inv_cancel₀ (hu j).ne', infScale_one']
      inv_val := funext fun j => by
        show infScale F (u j)⁻¹ * infScale F (u j) = 1
        rw [infScale_mul', inv_mul_cancel₀ (hu j).ne', infScale_one'] }
  have hχ : ((distribHaarChar (κ → AF F) s : ℝ≥0) : ℝ) = ∏ j, u j ^ Module.finrank ℚ F := by
    rw [GlobalTheory.ModuPiLocal.distribHaarChar_pi (fun _ : κ => AF F), NNReal.coe_prod]
    exact Finset.prod_congr rfl fun j _ => distribHaarChar_infScale F (u j) (hu j) _ rfl
  have h1 : μ.map (fun x => s • x) = DomMulAct.mk s⁻¹ • μ := by
    ext A hA
    rw [Measure.map_apply (measurable_const_smul s) hA, Measure.domSMul_apply, Equiv.symm_apply_apply,
      Set.preimage_smul]
  have h2 : μ.map (fun x => s • x) = ((distribHaarChar (κ → AF F) s)⁻¹ : ℝ≥0) • μ := by
    rw [h1, Measure.isAddLeftInvariant_eq_smul (DomMulAct.mk s⁻¹ • μ) μ,
      addHaarScalarFactor_smul_eq_distribHaarChar, map_inv]
  have h3 : ∫⁻ x, f (fun j => infScale F (u j) * x j) ∂μ = ∫⁻ y, f y ∂(μ.map (fun x => s • x)) :=
    (lintegral_map_equiv f (Homeomorph.smul s).toMeasurableEquiv).symm
  rw [h3, h2, ENNReal.smul_def, lintegral_smul_measure, smul_eq_mul, ← hχ, ENNReal.ofReal_coe_nnreal,
    ENNReal.coe_inv (distribHaarChar_pos).ne']

end GlobalTheory.TorusTheta
