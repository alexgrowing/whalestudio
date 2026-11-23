import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicUnitriangularMulMemUnipotentTimesIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModulusOfNormEqAbs
import GroundTheory.GlobalFields.TateThesis.NonvanishingPrimes
import GroundTheory.AutomorphicForms.ReductionMeasure

open NumberField IsDedekindDomain Matrix Formalism.UG GlobalTheory.CuspRep MeasureTheory
open scoped ENNReal
open scoped Pointwise

namespace GlobalTheory.AdeleScale

variable {E : Type} [Field E] [NumberField E]

theorem qV_ne_zero (v : HeightOneSpectrum (𝓞 E)) : (qV E v : ℝ) ≠ 0 := by
  rw [qV, Nat.cast_ne_zero, Ne, Ideal.absNorm_eq_zero_iff]
  exact v.ne_bot

theorem finId_adl_snd (ϖ : ∀ v : HeightOneSpectrum (𝓞 E), (v.adicCompletion E)ˣ) (m : HeightOneSpectrum (𝓞 E) →₀ ℤ)
    (v : HeightOneSpectrum (𝓞 E)) :
    ((finId E (GlobalTheory.CellDec.adl ϖ m) : AdeleRing (𝓞 E) E)).2 v = ((ϖ v ^ m v : (v.adicCompletion E)ˣ) : v.adicCompletion E) := by
  change ((1 : Af E) - 1 + ((GlobalTheory.CellDec.adl ϖ m : (Af E)ˣ) : Af E)) v = _
  rw [sub_self, zero_add]
  rfl

theorem finId_fst (a : (Af E)ˣ) : ((finId E a : AdeleRing (𝓞 E) E)).1 = 1 := by
  change (1 : InfiniteAdeleRing E) - 0 + 0 = 1
  rw [sub_zero, add_zero]

theorem ideleModule_finId_adl (ϖ : ∀ v : HeightOneSpectrum (𝓞 E), (v.adicCompletion E)ˣ)
    (hϖ : ∀ v, IsUnifV E v (ϖ v : v.adicCompletion E)) (m : HeightOneSpectrum (𝓞 E) →₀ ℤ)
    (s : Finset (HeightOneSpectrum (𝓞 E))) (hs : ∀ v, v ∉ s → m v = 0) :
    (GroundTheory.Global.IdeleGroup.ideleModule E (finId E (GlobalTheory.CellDec.adl ϖ m)) : ℝ) =
      ∏ v ∈ s, ((qV E v : ℝ) ^ m v)⁻¹ := by
  rw [GroundTheory.Global.IdeleGroup.ideleModule_eq]
  have h1 : ∀ w : InfinitePlace E,
      ‖((finId E (GlobalTheory.CellDec.adl ϖ m) : AdeleRing (𝓞 E) E)).1 w‖ ^ w.mult = 1 := fun w => by
    rw [finId_fst]
    change ‖(1 : w.Completion)‖ ^ w.mult = 1
    rw [norm_one, one_pow]
  have h2 : ∀ v : HeightOneSpectrum (𝓞 E),
      ‖((finId E (GlobalTheory.CellDec.adl ϖ m) : AdeleRing (𝓞 E) E)).2 v‖ = ((qV E v : ℝ) ^ m v)⁻¹ := fun v => by
    have hu : Valued.v ((ϖ v : (v.adicCompletion E)ˣ) : v.adicCompletion E) = WithZero.exp (-1 : ℤ) := hϖ v
    rw [finId_adl_snd, Units.val_zpow_eq_zpow_val, norm_zpow, GroundTheory.Global.norm_uniformizer hu, _root_.inv_zpow]
    rfl
  rw [Finset.prod_eq_one fun w _ => h1 w, one_mul]
  simp_rw [h2]
  refine finprod_eq_prod_of_mulSupport_subset _ fun v hv => ?_
  by_contra hvs
  exact hv (by show ((qV E v : ℝ) ^ m v)⁻¹ = 1; rw [hs v hvs, zpow_zero, inv_one])

end GlobalTheory.AdeleScale

open GlobalTheory.AdeleScale in

theorem GlobalTheory.AdeleScale.map_mul_finId_adl : ∀ (E : Type) [Field E] [NumberField E] (ϖ : ∀ v : HeightOneSpectrum (𝓞 E), (v.adicCompletion E)ˣ),
    (∀ v, IsUnifV E v (ϖ v : v.adicCompletion E)) → ∀ (m : HeightOneSpectrum (𝓞 E) →₀ ℤ)
    (s : Finset (HeightOneSpectrum (𝓞 E))), (∀ v, v ∉ s → m v = 0) →
    ∀ [MeasurableSpace (AdeleRing (𝓞 E) E)] [BorelSpace (AdeleRing (𝓞 E) E)] (μR : Measure (AdeleRing (𝓞 E) E)) [μR.IsAddHaarMeasure],
    Measure.map (fun x : AdeleRing (𝓞 E) E => ((finId E (GlobalTheory.CellDec.adl ϖ m) : (AdeleRing (𝓞 E) E)ˣ) : AdeleRing (𝓞 E) E) * x) μR =
      ENNReal.ofReal (∏ v ∈ s, (qV E v : ℝ) ^ m v) • μR := by
  intro E _ _ ϖ hϖ m s hs _ _ μR _
  set a : (AdeleRing (𝓞 E) E)ˣ := finId E (GlobalTheory.CellDec.adl ϖ m) with ha
  have hm : Measurable fun x : AdeleRing (𝓞 E) E => (a : AdeleRing (𝓞 E) E) * x :=
    (continuous_const.mul continuous_id).measurable
  have hchar : distribHaarChar (AdeleRing (𝓞 E) E) a • μR.map (fun x => (a : AdeleRing (𝓞 E) E) * x) = μR := by
    ext S hS
    rw [Measure.smul_apply, Measure.map_apply hm hS]
    have h1 := distribHaarChar_mul μR a ((fun x : AdeleRing (𝓞 E) E => (a : AdeleRing (𝓞 E) E) * x) ⁻¹' S)
    have e : a • ((fun x : AdeleRing (𝓞 E) E => (a : AdeleRing (𝓞 E) E) * x) ⁻¹' S) = S := by
      ext y
      rw [Set.mem_smul_set_iff_inv_smul_mem]
      simp [Units.smul_def]
    rw [e] at h1
    rw [ENNReal.smul_def, smul_eq_mul]
    exact h1
  have hmod : (distribHaarChar (AdeleRing (𝓞 E) E) a : ℝ) = ∏ v ∈ s, ((qV E v : ℝ) ^ m v)⁻¹ := by
    rw [GlobalTheory.ModuAdele.distribHaarChar_adeleRing]
    exact ideleModule_finId_adl ϖ hϖ m s hs
  have hone : ENNReal.ofReal (∏ v ∈ s, (qV E v : ℝ) ^ m v) * (distribHaarChar (AdeleRing (𝓞 E) E) a : ℝ≥0∞) = 1 := by
    rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (Finset.prod_nonneg fun v _ =>
      zpow_nonneg (Nat.cast_nonneg _) _), hmod, ← Finset.prod_mul_distrib,
      Finset.prod_eq_one fun v _ => mul_inv_cancel₀ (zpow_ne_zero _ (qV_ne_zero v)), ENNReal.ofReal_one]
  conv_rhs => rw [← hchar]
  rw [ENNReal.smul_def (distribHaarChar (AdeleRing (𝓞 E) E) a), smul_smul, hone, one_smul]
