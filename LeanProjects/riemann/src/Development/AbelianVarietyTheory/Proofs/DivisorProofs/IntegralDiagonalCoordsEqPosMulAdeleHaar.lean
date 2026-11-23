import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiagonalLagrangianInvariantForm
import GroundTheory.AutomorphicForms.GL2.GJMatrixAdelic
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct FourierTransform
open MeasureTheory GroundTheory.Automorphic.GJMatrix

noncomputable section
namespace GlobalTheory.DiagFormGlue

open GlobalTheory.DiagForm

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

attribute [local instance] GlobalTheory.AdelicUnitaryTop.locallyCompact_finiteAdele
  GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField

theorem shiftOf_glue (p : Vi F κ × Vf F κ) : shiftOf (glue p) = p := by
  refine Prod.ext ?_ rfl
  simp [shiftOf, glue]

theorem glue_shiftOf (x : κ → AdeleRing (𝓞 F) F) : glue (shiftOf x) = x := by
  funext i
  refine Prod.ext ?_ rfl
  show (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (eI F κ ((eI F κ).symm _) i) = (x i).1
  rw [ContinuousLinearEquiv.apply_symm_apply]
  exact RingEquiv.symm_apply_apply _ _

theorem glue_add (p q : Vi F κ × Vf F κ) : glue (p + q) = glue p + glue q := by
  conv_lhs => rw [← shiftOf_glue q]
  exact glue_add_shiftOf p (glue q)

theorem ringEquiv_symm_eq :
    ⇑(InfiniteAdeleRing.ringEquiv_mixedSpace F).symm = ⇑(GroundTheory.Global.homeomorphMixedSpace F).symm := by
  funext z
  apply (GroundTheory.Global.homeomorphMixedSpace F).injective
  rw [Homeomorph.apply_symm_apply, GroundTheory.Global.homeomorphMixedSpace_apply, RingEquiv.apply_symm_apply]

theorem continuous_glue : Continuous (glue : Vi F κ × Vf F κ → κ → AdeleRing (𝓞 F) F) := by
  refine continuous_pi fun i => ?_
  show Continuous fun p : Vi F κ × Vf F κ =>
    (((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (eI F κ p.1 i), p.2 i) :
      InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F)
  rw [ringEquiv_symm_eq]
  exact ((GroundTheory.Global.homeomorphMixedSpace F).symm.continuous.comp
    ((continuous_apply i).comp ((eI F κ).continuous.comp continuous_fst))).prodMk
    ((continuous_apply i).comp continuous_snd)

theorem continuous_shiftOf : Continuous (shiftOf : (κ → AdeleRing (𝓞 F) F) → Vi F κ × Vf F κ) := by
  refine Continuous.prodMk ((eI F κ).symm.continuous.comp (continuous_pi fun i => ?_))
    (continuous_pi fun i => continuous_snd.comp (continuous_apply i))
  show Continuous fun x : κ → AdeleRing (𝓞 F) F => GroundTheory.Global.homeomorphMixedSpace F (x i).1
  exact (GroundTheory.Global.homeomorphMixedSpace F).continuous.comp (continuous_fst.comp (continuous_apply i))

variable (F κ) in

def glueEquiv : (Vi F κ × Vf F κ) ≃+ (κ → AdeleRing (𝓞 F) F) where
  toFun := glue
  invFun := shiftOf
  left_inv := shiftOf_glue
  right_inv := glue_shiftOf
  map_add' := glue_add

theorem exists_glue_measure :
    letI : MeasurableSpace (AdeleRing (𝓞 F) F) := GroundTheory.Global.measurableSpace_adeleRing F
    ∃ c : NNReal, 0 < c ∧ (mu F κ).map glue = c • (adeleMeasurePi F (ι := κ)) := by
  letI : MeasurableSpace (AdeleRing (𝓞 F) F) := GroundTheory.Global.measurableSpace_adeleRing F
  haveI : BorelSpace (AdeleRing (𝓞 F) F) := GroundTheory.Global.borelSpace_adeleRing F
  haveI := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele F
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  haveI : (mu F κ).IsAddHaarMeasure := by unfold mu; infer_instance
  haveI : ((mu F κ).map (glueEquiv F κ)).IsAddHaarMeasure :=
    AddEquiv.isAddHaarMeasure_map _ (glueEquiv F κ) continuous_glue continuous_shiftOf
  have h := Measure.isAddLeftInvariant_eq_smul ((mu F κ).map (glueEquiv F κ)) (adeleMeasurePi F (ι := κ))
  refine ⟨_, ?_, h⟩
  refine pos_iff_ne_zero.2 fun h0 => ?_
  rw [h0, zero_smul] at h
  exact (Measure.IsAddHaarMeasure.toIsOpenPosMeasure (μ := (mu F κ).map (glueEquiv F κ))).open_pos
    Set.univ isOpen_univ Set.univ_nonempty (by rw [h]; rfl)

variable (F κ) in

def glueMEquiv :
    letI : MeasurableSpace (AdeleRing (𝓞 F) F) := GroundTheory.Global.measurableSpace_adeleRing F
    (Vi F κ × Vf F κ) ≃ᵐ (κ → AdeleRing (𝓞 F) F) :=
  letI : MeasurableSpace (AdeleRing (𝓞 F) F) := GroundTheory.Global.measurableSpace_adeleRing F
  haveI : BorelSpace (AdeleRing (𝓞 F) F) := GroundTheory.Global.borelSpace_adeleRing F
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  (Homeomorph.mk (glueEquiv F κ).toEquiv continuous_glue continuous_shiftOf).toMeasurableEquiv

end GlobalTheory.DiagFormGlue

namespace GlobalTheory

theorem diagForm_glue_integral : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ], ∃ c₀ : ℝ, 0 < c₀ ∧
    ∀ H : (κ → AF F) → ℂ, (Integrable (fun p => H (GlobalTheory.DiagForm.glue p)) (GlobalTheory.DiagForm.mu F κ) ↔
      Integrable H (adeleMeasurePi F)) ∧
      ∫ p, H (GlobalTheory.DiagForm.glue p) ∂(GlobalTheory.DiagForm.mu F κ) = c₀ * ∫ t, H t ∂(adeleMeasurePi F) := by
  intro F _ _ κ _
  letI : MeasurableSpace (AdeleRing (𝓞 F) F) := GroundTheory.Global.measurableSpace_adeleRing F
  obtain ⟨c, hc, hmap⟩ := DiagFormGlue.exists_glue_measure (F := F) (κ := κ)
  have hmap' : (GlobalTheory.DiagForm.mu F κ).map (DiagFormGlue.glueMEquiv F κ) = c • adeleMeasurePi F (ι := κ) := hmap
  refine ⟨c, hc, fun H => ⟨?_, ?_⟩⟩
  · rw [← (integrable_smul_measure (f := H) (μ := adeleMeasurePi F (ι := κ)) (c := (c : ENNReal))
      (by exact_mod_cast hc.ne') ENNReal.coe_ne_top)]
    have e2 : (c : ENNReal) • adeleMeasurePi F (ι := κ) = c • adeleMeasurePi F (ι := κ) := rfl
    rw [e2, ← hmap', integrable_map_equiv]
    rfl
  · have h1 := integral_map_equiv (μ := GlobalTheory.DiagForm.mu F κ) (DiagFormGlue.glueMEquiv F κ) H
    rw [hmap', integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul] at h1
    exact h1.symm
end GlobalTheory
