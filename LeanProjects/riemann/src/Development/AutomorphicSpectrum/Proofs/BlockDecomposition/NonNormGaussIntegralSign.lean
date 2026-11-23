import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.LocalWhittakerDuality.WSteps
import GroundTheory.LocalFields.QuadraticAbelian.WeilRepQuadratic
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnstatedLocalWeilLemma

open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData
open GroundTheory.LocalField.FiltrationCocycleLiftCriterion.WeilRep
open scoped ValuativeRel

noncomputable section

namespace GlobalTheory.CompanionTheory.WeilPush

section One

variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [MeasurableSpace K] [BorelSpace K]

theorem setLIntegral_compl_zero_indicator {T : Set K} (hT : MeasurableSet T) :
    ∫⁻ x in {0}ᶜ, T.indicator 1 x ∂(haarIntegers K) = haarIntegers K T := by
  have h : (haarIntegers K).restrict ({0}ᶜ : Set K) = haarIntegers K :=
    Measure.restrict_eq_self_of_ae_mem
      ((measure_eq_zero_iff_ae_notMem.mp haarIntegers_singleton_zero).mono fun x hx => hx)
  rw [h, lintegral_indicator_one hT]

end One

section Main

variable {F E : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]
  [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [MeasurableSpace E] [BorelSpace E] [Algebra F E]
  [ValuativeExtension F E] [FiniteDimensional F E] [Algebra.IsSeparable F E]
  [Fact (Module.finrank F E = 2)]

def gS (S : Set F) (y : F) : ENNReal := S.indicator 1 y * (modulus y : ENNReal)

theorem measurable_gS {S : Set F} (hS : MeasurableSet S) : Measurable (gS S) :=
  (measurable_one.indicator hS).mul measurable_modulus.coe_nnreal_ennreal

theorem lintegral_gS {S : Set F} (hS : MeasurableSet S) :
    ∫⁻ u : Fˣ, gS S (u : F) ∂(multHaar F) = multHaarConst F * haarIntegers F S := by
  rw [lintegral_multHaar (measurable_gS hS), ← setLIntegral_compl_zero_indicator hS]
  congr 1
  refine setLIntegral_congr_fun (measurableSet_singleton 0).compl fun x hx => ?_
  have h0 : (modulus x : ENNReal) ≠ 0 := by exact_mod_cast (modulus_pos hx).ne'
  simp only [gS]
  rw [mul_comm (S.indicator 1 x), ← mul_assoc, ENNReal.inv_mul_cancel h0 ENNReal.coe_ne_top, one_mul]

theorem continuous_normUnits (h : Continuous (algebraMap F E)) : Continuous (normUnits F E) := by
  have hN := GlobalTheory.CompanionTheory.WeilSB.continuous_norm_of (F := F) (E := E) h
  rw [Units.continuous_iff]
  refine ⟨?_, ?_⟩
  · have e : (Units.val ∘ (normUnits F E) : Eˣ → F) = fun x : Eˣ => Algebra.norm F (x : E) :=
      funext fun x => coe_normUnits x
    rw [e]
    exact hN.comp Units.continuous_val
  · have e : (fun x : Eˣ => (((normUnits F E x)⁻¹ : Fˣ) : F)) =
        fun x : Eˣ => Algebra.norm F ((x⁻¹ : Eˣ) : E) := funext fun x => by
      rw [← map_inv, coe_normUnits]
    show Continuous (fun x : Eˣ => (((normUnits F E x)⁻¹ : Fˣ) : F))
    rw [e]
    exact hN.comp (Units.continuous_val.comp continuous_inv)

theorem lintegral_gS_norm (h : Continuous (algebraMap F E)) (c : Fˣ) {S : Set F}
    (hS : MeasurableSet S) :
    ∫⁻ u : Eˣ, gS S ((c : F) * Algebra.norm F (u : E)) ∂(multHaar E) =
      multHaarConst E * ((modulus (c : F) : ENNReal) *
        haarIntegers E ((fun u : E => (c : F) * Algebra.norm F u) ⁻¹' S)) := by
  have hN := GlobalTheory.CompanionTheory.WeilSB.continuous_norm_of (F := F) (E := E) h
  have hm : Measurable (fun u : E => (c : F) * Algebra.norm F u) :=
    (continuous_const.mul hN).measurable
  have hT : MeasurableSet ((fun u : E => (c : F) * Algebra.norm F u) ⁻¹' S) := hm hS
  rw [lintegral_multHaar (g := fun x : E => gS S ((c : F) * Algebra.norm F x))
    ((measurable_gS hS).comp hm), ← setLIntegral_compl_zero_indicator hT,
    ← lintegral_const_mul _ (measurable_one.indicator hT)]
  congr 1
  refine setLIntegral_congr_fun (measurableSet_singleton 0).compl fun x hx => ?_
  have h0 : (modulus x : ENNReal) ≠ 0 := by exact_mod_cast (modulus_pos hx).ne'
  have hmod : (modulus ((c : F) * Algebra.norm F x) : ENNReal) =
      (modulus (c : F) : ENNReal) * (modulus x : ENNReal) := by
    rw [modulus_mul, modulus_norm]; push_cast; rfl
  have hi : (((fun u : E => (c : F) * Algebra.norm F u) ⁻¹' S).indicator 1 x : ENNReal) =
      S.indicator 1 ((c : F) * Algebra.norm F x) := rfl
  simp only [gS]
  rw [hmod, hi]
  calc _ = ((modulus x : ENNReal))⁻¹ * (modulus x : ENNReal) *
        (S.indicator 1 ((c : F) * Algebra.norm F x) * (modulus (c : F) : ENNReal)) := by ring
    _ = _ := by rw [ENNReal.inv_mul_cancel h0 ENNReal.coe_ne_top, one_mul, mul_comm]

theorem haar_identity (h : Continuous (algebraMap F E)) (a : Fˣ) (κ₀ : NNReal)
    (H : (multHaar E).map (normUnits F E) + (multHaar E).map (fun x => a * normUnits F E x) =
      κ₀ • multHaar F) {S : Set F} (hS : MeasurableSet S) :
    multHaarConst E * (haarIntegers E ((Algebra.norm F : E → F) ⁻¹' S) +
      (modulus (a : F) : ENNReal) * haarIntegers E ((fun u : E => (a : F) * Algebra.norm F u) ⁻¹' S)) =
    (κ₀ : ENNReal) * multHaarConst F * haarIntegers F S := by
  have hc := continuous_normUnits (F := F) (E := E) h
  have hm1 : Measurable (normUnits F E) := hc.measurable
  have hm2 : Measurable (fun x : Eˣ => a * normUnits F E x) := (continuous_const.mul hc).measurable
  have hg : Measurable (fun u : Fˣ => gS S (u : F)) :=
    (measurable_gS hS).comp Units.continuous_val.measurable
  have key := congrArg (fun μ : Measure Fˣ => ∫⁻ u, gS S (u : F) ∂μ) H
  rw [lintegral_add_measure, lintegral_map hg hm1, lintegral_map hg hm2, lintegral_smul_measure,
    lintegral_gS hS] at key
  have e1 : ∫⁻ u : Eˣ, gS S ((normUnits F E u : Fˣ) : F) ∂(multHaar E) =
      multHaarConst E * haarIntegers E ((Algebra.norm F : E → F) ⁻¹' S) := by
    have := lintegral_gS_norm (F := F) (E := E) h 1 hS
    simpa [coe_normUnits, modulus_one] using this
  have e2 : ∫⁻ u : Eˣ, gS S (((a * normUnits F E u : Fˣ)) : F) ∂(multHaar E) =
      multHaarConst E * ((modulus (a : F) : ENNReal) *
        haarIntegers E ((fun u : E => (a : F) * Algebra.norm F u) ⁻¹' S)) := by
    have := lintegral_gS_norm (F := F) (E := E) h a hS
    simpa [coe_normUnits] using this
  rw [e1, e2] at key
  rw [mul_add, key, ENNReal.smul_def, smul_eq_mul, mul_assoc]

end Main

theorem push_of_multHaar
    (H : ∀ (F E : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
      [MeasurableSpace F] [BorelSpace F] [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
      [MeasurableSpace E] [BorelSpace E] [Algebra F E] [ValuativeExtension F E] [FiniteDimensional F E]
      [Algebra.IsSeparable F E] [Fact (Module.finrank F E = 2)], Continuous (algebraMap F E) → ∀ a : Fˣ, a ∉ (normUnits F E).range → ∃ κ : NNReal,
      (multHaar E).map (normUnits F E) + (multHaar E).map (fun x => a * normUnits F E x) = κ • multHaar F) :
    ∀ (F E : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
      [MeasurableSpace F] [BorelSpace F] [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
      [MeasurableSpace E] [BorelSpace E] [Algebra F E] [ValuativeExtension F E] [FiniteDimensional F E]
      [Algebra.IsSeparable F E] [Fact (Module.finrank F E = 2)], Continuous (algebraMap F E) → ∀ a : Fˣ, a ∉ (normUnits F E).range → ∃ κ : ENNReal, κ ≠ ⊤ ∧ ∀ S : Set F, MeasurableSet S →
      haarIntegers E ((Algebra.norm F : E → F) ⁻¹' S) + (modulus (a : F) : ENNReal) * haarIntegers E ((fun u : E => (a : F) * Algebra.norm F u) ⁻¹' S) = κ * haarIntegers F S := by
  intro F E _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hcont a ha
  obtain ⟨κ₀, hκ⟩ := H F E hcont a ha
  have hE0 := multHaarConst_ne_zero (K := E)
  have hEt := multHaarConst_ne_top (K := E)
  refine ⟨(multHaarConst E)⁻¹ * ((κ₀ : ENNReal) * multHaarConst F), ?_, fun S hS => ?_⟩
  · exact ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr hE0)
      (ENNReal.mul_ne_top ENNReal.coe_ne_top multHaarConst_ne_top)
  · have key := haar_identity (F := F) (E := E) hcont a κ₀ hκ hS
    rw [mul_assoc, ← key, ← mul_assoc, ENNReal.inv_mul_cancel hE0 hEt, one_mul]

end GlobalTheory.CompanionTheory.WeilPush
