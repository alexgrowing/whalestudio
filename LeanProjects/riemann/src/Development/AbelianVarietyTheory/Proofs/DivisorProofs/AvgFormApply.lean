import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.SiegelAvg

def IsHaarB {Y : Type} [AddGroup Y] [TopologicalSpace Y] (μ : @Measure Y (borel Y)) : Prop :=
  @Measure.IsAddHaarMeasure Y _ _ (borel Y) μ

variable {Y V : Type} [TopologicalSpace Y] [AddCommGroup V] [Module ℂ V]

def Conv (μ : @Measure Y (borel Y)) (L₁ : V →ₗ[ℂ] ℂ) (T : Y → V →ₗ[ℂ] V) (v : V) : Prop :=
  letI : MeasurableSpace Y := borel Y
  Integrable (fun y => L₁ (T y v)) μ

def convSub (μ : @Measure Y (borel Y)) (L₁ : V →ₗ[ℂ] ℂ) (T : Y → V →ₗ[ℂ] V) : Submodule ℂ V where
  carrier := {v | Conv μ L₁ T v}
  zero_mem' := by
    letI : MeasurableSpace Y := borel Y
    show Integrable (fun y => L₁ (T y 0)) μ
    simp only [map_zero]
    exact integrable_zero _ _ _
  add_mem' := by
    letI : MeasurableSpace Y := borel Y
    intro v w hv hw
    show Integrable (fun y => L₁ (T y (v + w))) μ
    simp only [map_add]
    exact Integrable.add hv hw
  smul_mem' := by
    letI : MeasurableSpace Y := borel Y
    intro c v hv
    show Integrable (fun y => L₁ (T y (c • v))) μ
    simp only [map_smul, smul_eq_mul]
    exact Integrable.const_mul hv c

def avg0 (μ : @Measure Y (borel Y)) (L₁ : V →ₗ[ℂ] ℂ) (T : Y → V →ₗ[ℂ] V) : convSub μ L₁ T →ₗ[ℂ] ℂ where
  toFun v := letI : MeasurableSpace Y := borel Y; ∫ y, L₁ (T y (v : V)) ∂μ
  map_add' v w := by
    letI : MeasurableSpace Y := borel Y
    show ∫ y, L₁ (T y ((v : V) + w)) ∂μ = ∫ y, L₁ (T y v) ∂μ + ∫ y, L₁ (T y w) ∂μ
    simp only [map_add]
    exact integral_add v.2 w.2
  map_smul' c v := by
    letI : MeasurableSpace Y := borel Y
    show ∫ y, L₁ (T y (c • (v : V))) ∂μ = c • ∫ y, L₁ (T y v) ∂μ
    simp only [map_smul, smul_eq_mul]
    exact integral_const_mul c _

def avgForm (μ : @Measure Y (borel Y)) (L₁ : V →ₗ[ℂ] ℂ) (T : Y → V →ₗ[ℂ] V) : V →ₗ[ℂ] ℂ :=
  (LinearMap.exists_extend (avg0 μ L₁ T)).choose

theorem avgForm_apply (μ : @Measure Y (borel Y)) (L₁ : V →ₗ[ℂ] ℂ) (T : Y → V →ₗ[ℂ] V) {v : V}
    (hv : Conv μ L₁ T v) :
    avgForm μ L₁ T v = (letI : MeasurableSpace Y := borel Y; ∫ y, L₁ (T y v) ∂μ) :=
  LinearMap.congr_fun (LinearMap.exists_extend (avg0 μ L₁ T)).choose_spec ⟨v, hv⟩

def schrL {R : Type} [CommRing R] [Invertible (2 : R)] (ψ : AddChar R ℂ) {κ : Type} [Fintype κ]
    (w : (κ → R) × (κ → R)) : Module.End ℂ ((κ → R) → ℂ) where
  toFun := schr ψ w
  map_add' φ φ' := funext fun x => by simp only [schr, Pi.add_apply]; ring
  map_smul' c φ := funext fun x => by simp only [schr, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

def starFam {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {a b : ℕ}
    {Bf : Matrix (Fin a) (Fin b ⊕ Fin b) (AE F E) → Matrix (Fin a) (Fin b ⊕ Fin b) (AE F E) → AF F} {κ : Type} [Fintype κ]
    (dd : Darboux Bf κ) (ψ : AddChar (AF F) ℂ) (u : Fin a → AE F E) (y : Fin b → AE F E) :
    Module.End ℂ ((κ → AF F) → ℂ) :=
  schrL ψ (dd.e (Matrix.vecMulVec u (Sum.elim y y)))

theorem starFam_apply {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {a b : ℕ}
    {Bf : Matrix (Fin a) (Fin b ⊕ Fin b) (AE F E) → Matrix (Fin a) (Fin b ⊕ Fin b) (AE F E) → AF F} {κ : Type} [Fintype κ]
    (dd : Darboux Bf κ) (ψ : AddChar (AF F) ℂ) (u : Fin a → AE F E) (y : Fin b → AE F E) (φ : (κ → AF F) → ℂ) :
    starFam dd ψ u y φ = dd.rho ψ (Matrix.vecMulVec u (Sum.elim y y)) φ := rfl

end GlobalTheory.SiegelAvg

end
