import Mathlib
import GroundTheory.AutomorphicForms.GL2.GJGlobalModulus
import GroundTheory.AutomorphicForms.GL2.GJMatrixSchwartz

namespace GroundTheory.Automorphic.GJGlobal

open NumberField NumberField.mixedEmbedding IsDedekindDomain MeasureTheory Measure Matrix
  GroundTheory.Global GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.GJMatrix
  GroundTheory.Automorphic.GJGlobal.Modulus
open scoped NumberField.AdeleRing ENNReal NNReal SchwartzMap Classical

noncomputable section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 1000

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

namespace Twist

def invMod (g : GL (Fin n) 𝔸[K]) : ℝ≥0 :=
  Real.toNNReal ((IdeleGroup.ideleModule K (Matrix.GeneralLinearGroup.det g) : ℝ))⁻¹

theorem coe_invMod (g : GL (Fin n) 𝔸[K]) :
    (invMod g : ℝ) = ((detModule K n g : ℝ))⁻¹ := by
  rw [invMod, Real.coe_toNNReal _ (inv_nonneg.2 (IdeleGroup.ideleModule K _).2.le)]
  rfl

theorem pi_const_smul {ι : Type*} [Fintype ι] {X : Type*} [MeasurableSpace X] (μ : Measure X)
    [SigmaFinite μ] (c : ℝ≥0) :
    Measure.pi (fun _ : ι => c • μ) = (c ^ Fintype.card ι) • Measure.pi (fun _ : ι => μ) := by
  refine pi_eq fun s hs => ?_
  rw [Measure.smul_apply, pi_pi, ENNReal.smul_def, smul_eq_mul]
  simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, ENNReal.coe_pow]

theorem map_mul_right (b : GL (Fin n) 𝔸[K]) :
    (adelicMatrixMeasure K n).map (fun x => x * (b : Matrix (Fin n) (Fin n) 𝔸[K])) =
      (invMod b ^ n) • adelicMatrixMeasure K n := by
  have hf : (fun x : Matrix (Fin n) (Fin n) 𝔸[K] => x * (b : Matrix (Fin n) (Fin n) 𝔸[K])) =
      fun x i => (x i) ᵥ* (b : Matrix (Fin n) (Fin n) 𝔸[K]) := by
    funext x i j
    simp [Matrix.mul_apply, Matrix.vecMul, dotProduct]
  have hmap : (adeleMeasurePi K (ι := Fin n)).map (fun y => y ᵥ* (b : Matrix (Fin n) (Fin n) 𝔸[K])) =
      invMod b • adeleMeasurePi K (ι := Fin n) := by
    rw [map_vecMul_adeleMeasurePi, invMod, ENNReal.smul_def]
    rfl
  have hsf : ∀ _ : Fin n, SigmaFinite ((adeleMeasurePi K (ι := Fin n)).map
      fun y => y ᵥ* (b : Matrix (Fin n) (Fin n) 𝔸[K])) := fun _ => by
    rw [hmap]; infer_instance
  rw [hf]
  change (Measure.pi fun _ : Fin n => adeleMeasurePi K (ι := Fin n)).map
    (fun x i => (x i) ᵥ* (b : Matrix (Fin n) (Fin n) 𝔸[K])) = _
  rw [pi_map_pi (hμ := hsf) (fun _ => (measurable_vecMul' b).aemeasurable)]
  simp only [hmap]
  rw [pi_const_smul, Fintype.card_fin]
  rfl

theorem measurePreserving_transpose :
    MeasurePreserving (fun x : Matrix (Fin n) (Fin n) 𝔸[K] => xᵀ) (adelicMatrixMeasure K n)
      (adelicMatrixMeasure K n) := by
  set e := (MeasurableEquiv.curry (Fin n) (Fin n) 𝔸[K]).symm
  have he : MeasurePreserving e (adelicMatrixMeasure K n)
      (Measure.pi fun _ : Fin n × Fin n => adeleMeasure K) :=
    measurePreserving_matrixCoord (n := Fin n) (adeleMeasure K)
  have hT := measurePreserving_matrixCoordT (n := Fin n) (adeleMeasure K)
  have h : (fun x : Matrix (Fin n) (Fin n) 𝔸[K] => xᵀ) = e.symm ∘ matrixCoordT := by
    funext x i j
    rfl
  rw [h]
  exact (he.symm e).comp hT

def transposeGL (a : GL (Fin n) 𝔸[K]) : GL (Fin n) 𝔸[K] :=
  ⟨(a : Matrix (Fin n) (Fin n) 𝔸[K])ᵀ, ((a⁻¹ : GL (Fin n) 𝔸[K]) : Matrix (Fin n) (Fin n) 𝔸[K])ᵀ,
    by rw [← transpose_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, transpose_one],
    by rw [← transpose_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, transpose_one]⟩

theorem coe_transposeGL (a : GL (Fin n) 𝔸[K]) :
    ((transposeGL a : GL (Fin n) 𝔸[K]) : Matrix (Fin n) (Fin n) 𝔸[K]) =
      (a : Matrix (Fin n) (Fin n) 𝔸[K])ᵀ := rfl

theorem invMod_transposeGL (a : GL (Fin n) 𝔸[K]) : invMod (transposeGL a) = invMod a := by
  have h : Matrix.GeneralLinearGroup.det (transposeGL a) = Matrix.GeneralLinearGroup.det a := by
    ext
    rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.val_det_apply,
      coe_transposeGL, det_transpose]
  rw [invMod, invMod, h]

theorem map_mul_left (a : GL (Fin n) 𝔸[K]) :
    (adelicMatrixMeasure K n).map (fun x => (a : Matrix (Fin n) (Fin n) 𝔸[K]) * x) =
      (invMod a ^ n) • adelicMatrixMeasure K n := by
  have hT := measurePreserving_transpose (K := K) (n := n)
  have hR : Measurable fun x : Matrix (Fin n) (Fin n) 𝔸[K] =>
      x * ((transposeGL a : GL (Fin n) 𝔸[K]) : Matrix (Fin n) (Fin n) 𝔸[K]) :=
    (continuous_id.matrix_mul continuous_const).measurable
  have h : (fun x : Matrix (Fin n) (Fin n) 𝔸[K] => (a : Matrix (Fin n) (Fin n) 𝔸[K]) * x) =
      (fun x => xᵀ) ∘ (fun x => x * ((transposeGL a : GL (Fin n) 𝔸[K]) :
        Matrix (Fin n) (Fin n) 𝔸[K])) ∘ (fun x => xᵀ) := by
    funext x
    simp only [Function.comp_apply, coe_transposeGL, ← transpose_mul, transpose_transpose]
  rw [h, ← map_map hT.measurable (hR.comp hT.measurable), ← map_map hR hT.measurable, hT.map_eq,
    map_mul_right, Measure.map_smul, hT.map_eq, invMod_transposeGL]

theorem map_mul_mul (a b : GL (Fin n) 𝔸[K]) :
    (adelicMatrixMeasure K n).map
        (fun x => (a : Matrix (Fin n) (Fin n) 𝔸[K]) * x * (b : Matrix (Fin n) (Fin n) 𝔸[K])) =
      ((invMod a * invMod b) ^ n) • adelicMatrixMeasure K n := by
  have hL : Measurable fun x : Matrix (Fin n) (Fin n) 𝔸[K] =>
      (a : Matrix (Fin n) (Fin n) 𝔸[K]) * x :=
    (continuous_const.matrix_mul continuous_id).measurable
  have hR : Measurable fun x : Matrix (Fin n) (Fin n) 𝔸[K] =>
      x * (b : Matrix (Fin n) (Fin n) 𝔸[K]) :=
    (continuous_id.matrix_mul continuous_const).measurable
  have h : (fun x : Matrix (Fin n) (Fin n) 𝔸[K] =>
      (a : Matrix (Fin n) (Fin n) 𝔸[K]) * x * (b : Matrix (Fin n) (Fin n) 𝔸[K])) =
      (fun x => x * (b : Matrix (Fin n) (Fin n) 𝔸[K])) ∘
        (fun x => (a : Matrix (Fin n) (Fin n) 𝔸[K]) * x) := rfl
  rw [h, ← map_map hR hL, map_mul_left, Measure.map_smul, map_mul_right, smul_smul, mul_pow,
    mul_comm]

def mulMulHomeomorph (a b : GL (Fin n) 𝔸[K]) :
    Matrix (Fin n) (Fin n) 𝔸[K] ≃ₜ Matrix (Fin n) (Fin n) 𝔸[K] where
  toFun x := (a : Matrix (Fin n) (Fin n) 𝔸[K]) * x * (b : Matrix (Fin n) (Fin n) 𝔸[K])
  invFun x := ((a⁻¹ : GL (Fin n) 𝔸[K]) : Matrix (Fin n) (Fin n) 𝔸[K]) * x *
    ((b⁻¹ : GL (Fin n) 𝔸[K]) : Matrix (Fin n) (Fin n) 𝔸[K])
  left_inv x := by
    simp only [← Matrix.mul_assoc]
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul, Matrix.mul_assoc,
      ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
  right_inv x := by
    simp only [← Matrix.mul_assoc]
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul, Matrix.mul_assoc,
      ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.mul_one]
  continuous_toFun := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  continuous_invFun := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const

theorem integral_comp_mul_mul (a b : GL (Fin n) 𝔸[K]) (f : Matrix (Fin n) (Fin n) 𝔸[K] → ℂ) :
    ∫ x, f ((a : Matrix (Fin n) (Fin n) 𝔸[K]) * x * (b : Matrix (Fin n) (Fin n) 𝔸[K]))
        ∂adelicMatrixMeasure K n =
      ((((detModule K n a : ℝ) * (detModule K n b : ℝ)) ^ n)⁻¹ : ℂ) *
        ∫ x, f x ∂adelicMatrixMeasure K n := by
  have hemb : MeasurableEmbedding (mulMulHomeomorph a b) :=
    (mulMulHomeomorph a b).toMeasurableEquiv.measurableEmbedding
  have h1 := hemb.integral_map (μ := adelicMatrixMeasure K n) f
  change ∫ x, f (mulMulHomeomorph a b x) ∂adelicMatrixMeasure K n = _
  rw [← h1]
  change ∫ y, f y ∂(adelicMatrixMeasure K n).map
    (fun x => (a : Matrix (Fin n) (Fin n) 𝔸[K]) * x * (b : Matrix (Fin n) (Fin n) 𝔸[K])) = _
  rw [map_mul_mul, integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul]
  congr 1
  push_cast
  rw [coe_invMod, coe_invMod]
  push_cast
  rw [← mul_inv, inv_pow]

def infHom : 𝔸[K] →+* mixedSpace K :=
  (InfiniteAdeleRing.ringEquiv_mixedSpace K).toRingHom.comp
    (RingHom.fst (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K))

def finHom : 𝔸[K] →+* FiniteAdeleRing (𝓞 K) K :=
  RingHom.snd (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K)

theorem infPartPi_eq' (z : Fin n × Fin n → 𝔸[K]) : infPartPi z = fun p => infHom (z p) := rfl

theorem finPartPi_eq' (z : Fin n × Fin n → 𝔸[K]) : finPartPi z = fun p => finHom (z p) := rfl

def twistCoord {R : Type*} [CommRing R] (A B : Matrix (Fin n) (Fin n) R)
    (z : Fin n × Fin n → R) : Fin n × Fin n → R :=
  matrixCoord (A * Matrix.of (fun i j => z (i, j)) * B)

theorem twistCoord_map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (A B : Matrix (Fin n) (Fin n) R) (z : Fin n × Fin n → R) :
    (fun p => f (twistCoord A B z p)) = twistCoord (A.map f) (B.map f) (fun p => f (z p)) := by
  have h : (A * Matrix.of (fun i j => z (i, j)) * B).map f =
      A.map f * Matrix.of (fun i j => f (z (i, j))) * B.map f := by
    rw [Matrix.map_mul, Matrix.map_mul]
    rfl
  funext p
  exact congrFun (congrFun h p.1) p.2

theorem twistCoord_twistCoord {R : Type*} [CommRing R] {A B A' B' : Matrix (Fin n) (Fin n) R}
    (hA : A' * A = 1) (hB : B * B' = 1) (z : Fin n × Fin n → R) :
    twistCoord A' B' (twistCoord A B z) = z := by
  have h1 : Matrix.of (fun i j => matrixCoord (A * Matrix.of (fun i j => z (i, j)) * B) (i, j)) =
      A * Matrix.of (fun i j => z (i, j)) * B := Matrix.ext fun i j => rfl
  have h2 : A' * (A * Matrix.of (fun i j => z (i, j)) * B) * B' =
      Matrix.of (fun i j => z (i, j)) := by
    calc A' * (A * Matrix.of (fun i j => z (i, j)) * B) * B' =
        (A' * A) * Matrix.of (fun i j => z (i, j)) * (B * B') := by
          simp only [Matrix.mul_assoc]
      _ = Matrix.of (fun i j => z (i, j)) := by rw [hA, hB, Matrix.one_mul, Matrix.mul_one]
  funext p
  simp only [twistCoord]
  rw [h1, h2]
  rfl

theorem continuous_twistCoord {R : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    (A B : Matrix (Fin n) (Fin n) R) : Continuous (twistCoord A B) :=
  (matrixCoordHomeomorph (Fin n) R).continuous.comp
    ((continuous_const.matrix_mul (matrixCoordHomeomorph (Fin n) R).symm.continuous).matrix_mul
      continuous_const)

theorem map_inv_mul_map {R : Type*} [CommRing R] (f : 𝔸[K] →+* R) (g : GL (Fin n) 𝔸[K]) :
    ((g⁻¹ : GL (Fin n) 𝔸[K]) : Matrix (Fin n) (Fin n) 𝔸[K]).map f *
      (g : Matrix (Fin n) (Fin n) 𝔸[K]).map f = 1 := by
  rw [← Matrix.map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
    Matrix.map_one f (map_zero f) (map_one f)]

theorem map_mul_map_inv {R : Type*} [CommRing R] (f : 𝔸[K] →+* R) (g : GL (Fin n) 𝔸[K]) :
    (g : Matrix (Fin n) (Fin n) 𝔸[K]).map f *
      ((g⁻¹ : GL (Fin n) 𝔸[K]) : Matrix (Fin n) (Fin n) 𝔸[K]).map f = 1 := by
  rw [← Matrix.map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
    Matrix.map_one f (map_zero f) (map_one f)]

def twistInfLin (a b : GL (Fin n) 𝔸[K]) :
    (Fin n × Fin n → mixedSpace K) ≃ₗ[ℝ] (Fin n × Fin n → mixedSpace K) where
  toFun := twistCoord ((a : Matrix (Fin n) (Fin n) 𝔸[K]).map infHom)
    ((b : Matrix (Fin n) (Fin n) 𝔸[K]).map infHom)
  invFun := twistCoord (((a⁻¹ : GL (Fin n) 𝔸[K]) : Matrix (Fin n) (Fin n) 𝔸[K]).map infHom)
    (((b⁻¹ : GL (Fin n) 𝔸[K]) : Matrix (Fin n) (Fin n) 𝔸[K]).map infHom)
  map_add' u v := by
    funext p
    simp only [twistCoord, matrixCoord, Pi.add_apply]
    have : Matrix.of (fun i j => u (i, j) + v (i, j)) =
        Matrix.of (fun i j => u (i, j)) + Matrix.of (fun i j => v (i, j)) :=
      Matrix.ext fun i j => rfl
    rw [this, Matrix.mul_add, Matrix.add_mul]
    rfl
  map_smul' c u := by
    funext p
    simp only [twistCoord, matrixCoord, Pi.smul_apply, RingHom.id_apply]
    have : Matrix.of (fun i j => c • u (i, j)) = c • Matrix.of (fun i j => u (i, j)) :=
      Matrix.ext fun i j => rfl
    rw [this, Matrix.mul_smul, Matrix.smul_mul]
    rfl
  left_inv u := twistCoord_twistCoord (map_inv_mul_map infHom a) (map_mul_map_inv infHom b) u
  right_inv u := twistCoord_twistCoord (map_mul_map_inv infHom a) (map_inv_mul_map infHom b) u

def twistInf (a b : GL (Fin n) 𝔸[K]) :
    (Fin n × Fin n → mixedSpace K) ≃L[ℝ] (Fin n × Fin n → mixedSpace K) :=
  (twistInfLin a b).toContinuousLinearEquiv

theorem coe_twistInf (a b : GL (Fin n) 𝔸[K]) :
    ⇑(twistInf a b) = twistCoord ((a : Matrix (Fin n) (Fin n) 𝔸[K]).map infHom)
      ((b : Matrix (Fin n) (Fin n) 𝔸[K]).map infHom) := rfl

def twistFin (a b : GL (Fin n) 𝔸[K]) :
    (Fin n × Fin n → FiniteAdeleRing (𝓞 K) K) ≃ₜ (Fin n × Fin n → FiniteAdeleRing (𝓞 K) K) where
  toFun := twistCoord ((a : Matrix (Fin n) (Fin n) 𝔸[K]).map finHom)
    ((b : Matrix (Fin n) (Fin n) 𝔸[K]).map finHom)
  invFun := twistCoord (((a⁻¹ : GL (Fin n) 𝔸[K]) : Matrix (Fin n) (Fin n) 𝔸[K]).map finHom)
    (((b⁻¹ : GL (Fin n) 𝔸[K]) : Matrix (Fin n) (Fin n) 𝔸[K]).map finHom)
  left_inv u := twistCoord_twistCoord (map_inv_mul_map finHom a) (map_mul_map_inv finHom b) u
  right_inv u := twistCoord_twistCoord (map_mul_map_inv finHom a) (map_inv_mul_map finHom b) u
  continuous_toFun := continuous_twistCoord _ _
  continuous_invFun := continuous_twistCoord _ _

theorem coe_twistFin (a b : GL (Fin n) 𝔸[K]) :
    ⇑(twistFin a b) = twistCoord ((a : Matrix (Fin n) (Fin n) 𝔸[K]).map finHom)
      ((b : Matrix (Fin n) (Fin n) 𝔸[K]).map finHom) := rfl

theorem tensor_comp_twistCoord (φ : 𝓢(Fin n × Fin n → mixedSpace K, ℂ))
    (g : (Fin n × Fin n → FiniteAdeleRing (𝓞 K) K) → ℂ) (a b : GL (Fin n) 𝔸[K]) :
    schwartzBruhatTensorPi φ g ∘ twistCoord (a : Matrix (Fin n) (Fin n) 𝔸[K])
        (b : Matrix (Fin n) (Fin n) 𝔸[K]) =
      schwartzBruhatTensorPi (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (twistInf a b) φ)
        (g ∘ twistFin a b) := by
  funext z
  simp only [Function.comp_apply, schwartzBruhatTensorPi,
    SchwartzMap.compCLMOfContinuousLinearEquiv_apply, coe_twistInf, coe_twistFin]
  rw [infPartPi_eq', infPartPi_eq', finPartPi_eq', finPartPi_eq', twistCoord_map infHom,
    twistCoord_map finHom]

theorem comp_twistCoord_mem {F : (Fin n × Fin n → 𝔸[K]) → ℂ}
    (hF : F ∈ schwartzBruhatPi K (Fin n × Fin n)) (a b : GL (Fin n) 𝔸[K]) :
    F ∘ twistCoord (a : Matrix (Fin n) (Fin n) 𝔸[K]) (b : Matrix (Fin n) (Fin n) 𝔸[K]) ∈
      schwartzBruhatPi K (Fin n × Fin n) := by
  induction hF using Submodule.span_induction with
  | mem G hG =>
    obtain ⟨φ, g, hg, rfl⟩ := hG
    rw [tensor_comp_twistCoord]
    refine schwartzBruhatTensorPi_mem _ ((mem_finiteSchwartzBruhatPi K).2 ⟨?_, ?_⟩)
    · exact ((mem_finiteSchwartzBruhatPi K).1 hg).1.comp_continuous (twistFin a b).continuous
    · exact ((mem_finiteSchwartzBruhatPi K).1 hg).2.comp_homeomorph (twistFin a b)
  | zero => exact zero_mem _
  | add G H _ _ hG hH => exact add_mem hG hH
  | smul c G _ hG => exact Submodule.smul_mem _ c hG

end Twist

open Twist

theorem mul_mul_mem_matrixSchwartzBruhat {Φ : Matrix (Fin n) (Fin n) 𝔸[K] → ℂ}
    (hΦ : Φ ∈ matrixSchwartzBruhat K n) (a b : GL (Fin n) 𝔸[K]) :
    (fun x => Φ ((a : Matrix (Fin n) (Fin n) 𝔸[K]) * x * (b : Matrix (Fin n) (Fin n) 𝔸[K]))) ∈
      matrixSchwartzBruhat K n := by
  rw [mem_matrixSchwartzBruhat] at hΦ ⊢
  have h := comp_twistCoord_mem hΦ a b
  convert h using 1
  funext z
  rfl

theorem adelicMatrixFourier_mul_mul (Φ : Matrix (Fin n) (Fin n) 𝔸[K] → ℂ) (a b : GL (Fin n) 𝔸[K])
    (y : Matrix (Fin n) (Fin n) 𝔸[K]) :
    adelicMatrixFourier K
        (fun x => Φ ((a : Matrix (Fin n) (Fin n) 𝔸[K]) * x * (b : Matrix (Fin n) (Fin n) 𝔸[K]))) y =
      ((((detModule K n a : ℝ) * (detModule K n b : ℝ)) ^ n)⁻¹ : ℂ) *
        adelicMatrixFourier K Φ (((b⁻¹ : GL (Fin n) 𝔸[K]) : Matrix (Fin n) (Fin n) 𝔸[K]) * y *
          ((a⁻¹ : GL (Fin n) 𝔸[K]) : Matrix (Fin n) (Fin n) 𝔸[K])) := by
  set A : Matrix (Fin n) (Fin n) 𝔸[K] := (a : Matrix (Fin n) (Fin n) 𝔸[K])
  set B : Matrix (Fin n) (Fin n) 𝔸[K] := (b : Matrix (Fin n) (Fin n) 𝔸[K])
  set A' : Matrix (Fin n) (Fin n) 𝔸[K] := ((a⁻¹ : GL (Fin n) 𝔸[K]) : Matrix (Fin n) (Fin n) 𝔸[K])
  set B' : Matrix (Fin n) (Fin n) 𝔸[K] := ((b⁻¹ : GL (Fin n) 𝔸[K]) : Matrix (Fin n) (Fin n) 𝔸[K])
  have hA : A' * A = 1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hB : B * B' = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have htr : ∀ x : Matrix (Fin n) (Fin n) 𝔸[K], Matrix.trace (A * x * B * (B' * y * A')) = Matrix.trace (x * y) := by
    intro x
    have e1 : A * x * B * (B' * y * A') = A * (x * (y * A')) := by
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc B B', hB, Matrix.one_mul]
    rw [e1, Matrix.trace_mul_comm]
    simp only [Matrix.mul_assoc]
    rw [hA, Matrix.mul_one]
  rw [adelicMatrixFourier, adelicMatrixFourier, ← integral_comp_mul_mul a b]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only
  rw [htr]

theorem twisted_poisson {Φ : Matrix (Fin n) (Fin n) 𝔸[K] → ℂ} (hΦ : Φ ∈ matrixSchwartzBruhat K n)
    (a b : AdelicGLn.AdelicGL K n) :
    Summable (fun ξ : Matrix (Fin n) (Fin n) K =>
      ‖Φ ((a : Matrix (Fin n) (Fin n) 𝔸[K]) * ratMat ξ * (b : Matrix (Fin n) (Fin n) 𝔸[K]))‖) ∧
    Summable (fun ξ : Matrix (Fin n) (Fin n) K =>
      ‖adelicMatrixFourier K Φ (((b⁻¹ : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]) *
        ratMat ξ * ((a⁻¹ : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]))‖) ∧
    ∑' ξ : Matrix (Fin n) (Fin n) K,
        Φ ((a : Matrix (Fin n) (Fin n) 𝔸[K]) * ratMat ξ * (b : Matrix (Fin n) (Fin n) 𝔸[K])) =
      ((((detModule K n a : ℝ) * (detModule K n b : ℝ)) ^ n)⁻¹ : ℂ) *
        ∑' ξ : Matrix (Fin n) (Fin n) K,
          adelicMatrixFourier K Φ (((b⁻¹ : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]) *
            ratMat ξ * ((a⁻¹ : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K])) := by
  set c : ℂ := ((((detModule K n a : ℝ) * (detModule K n b : ℝ)) ^ n)⁻¹ : ℂ) with hc
  have hc0 : c ≠ 0 := by
    rw [hc]
    refine inv_ne_zero (pow_ne_zero _ (mul_ne_zero ?_ ?_))
    · exact_mod_cast (detModule K n a).2.ne'
    · exact_mod_cast (detModule K n b).2.ne'
  obtain ⟨h1, h2, h3⟩ := poisson_matrix (mul_mul_mem_matrixSchwartzBruhat hΦ a b)
  have hF : ∀ ξ : Matrix (Fin n) (Fin n) K,
      adelicMatrixFourier K (fun x => Φ ((a : Matrix (Fin n) (Fin n) 𝔸[K]) * x *
        (b : Matrix (Fin n) (Fin n) 𝔸[K]))) (ξ.map (algebraMap K 𝔸[K])) =
      c * adelicMatrixFourier K Φ (((b⁻¹ : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]) *
        ξ.map (algebraMap K 𝔸[K]) * ((a⁻¹ : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K])) :=
    fun ξ => adelicMatrixFourier_mul_mul Φ a b _
  simp only [ratMat]
  simp only [hF] at h2 h3
  refine ⟨h1, ?_, ?_⟩
  · have h2' := h2.mul_left (‖c‖⁻¹)
    refine h2'.congr fun ξ => ?_
    rw [norm_mul, ← mul_assoc, inv_mul_cancel₀ (norm_ne_zero_iff.2 hc0), one_mul]
  · rw [h3, tsum_mul_left]

theorem centralSection_mul_comm_matrix (t : {r : ℝ // 0 < r}) (M : Matrix (Fin n) (Fin n) 𝔸[K]) :
    ((centralSection K n t : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]) * M =
      M * ((centralSection K n t : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]) := by
  rw [centralSection, MonoidHom.comp_apply, scalarUnits_apply, coe_diagUnits]
  exact (Matrix.scalar_commute _ (fun _ => Commute.all _ _) M)

theorem twisted_poisson_centralSection (hn : 0 < n) {Φ : Matrix (Fin n) (Fin n) 𝔸[K] → ℂ}
    (hΦ : Φ ∈ matrixSchwartzBruhat K n) (t : {r : ℝ // 0 < r}) {x y : AdelicGLn.AdelicGL K n}
    (hx : x ∈ normOneGL K n) (hy : y ∈ normOneGL K n) :
    Summable (fun ξ : Matrix (Fin n) (Fin n) K =>
      ‖Φ (((centralSection K n t * x⁻¹ : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]) *
        ratMat ξ * (y : Matrix (Fin n) (Fin n) 𝔸[K]))‖) ∧
    Summable (fun ξ : Matrix (Fin n) (Fin n) K =>
      ‖adelicMatrixFourier K Φ (((centralSection K n t⁻¹ * y⁻¹ : AdelicGLn.AdelicGL K n) :
        Matrix (Fin n) (Fin n) 𝔸[K]) * ratMat ξ * (x : Matrix (Fin n) (Fin n) 𝔸[K]))‖) ∧
    ∑' ξ : Matrix (Fin n) (Fin n) K,
        Φ (((centralSection K n t * x⁻¹ : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]) *
          ratMat ξ * (y : Matrix (Fin n) (Fin n) 𝔸[K])) =
      ((((t : ℝ)) ^ n)⁻¹ : ℂ) *
        ∑' ξ : Matrix (Fin n) (Fin n) K,
          adelicMatrixFourier K Φ (((centralSection K n t⁻¹ * y⁻¹ : AdelicGLn.AdelicGL K n) :
            Matrix (Fin n) (Fin n) 𝔸[K]) * ratMat ξ * (x : Matrix (Fin n) (Fin n) 𝔸[K])) := by
  obtain ⟨h1, h2, h3⟩ := twisted_poisson hΦ (centralSection K n t * x⁻¹) y
  have hxm : detModule K n x = 1 := mem_normOneGL_iff_detModule.1 hx
  have hym : detModule K n y = 1 := mem_normOneGL_iff_detModule.1 hy
  have hdet : ((detModule K n (centralSection K n t * x⁻¹) : ℝ) * (detModule K n y : ℝ)) =
      (t : ℝ) := by
    rw [map_mul, map_inv, hxm, hym, detModule_centralSection hn, inv_one, mul_one, Positive.val_one,
      mul_one]
  have harg : ∀ ξ : Matrix (Fin n) (Fin n) K,
      ((y⁻¹ : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]) * ratMat ξ *
        (((centralSection K n t * x⁻¹)⁻¹ : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]) =
      ((centralSection K n t⁻¹ * y⁻¹ : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]) *
        ratMat ξ * (x : Matrix (Fin n) (Fin n) 𝔸[K]) := by
    intro ξ
    rw [_root_.mul_inv_rev, inv_inv, ← map_inv, Units.val_mul, Units.val_mul]
    set Z : Matrix (Fin n) (Fin n) 𝔸[K] :=
      ((centralSection K n t⁻¹ : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K])
    have hz := centralSection_mul_comm_matrix (K := K) (n := n) t⁻¹
    calc ((y⁻¹ : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]) * ratMat ξ *
          ((x : Matrix (Fin n) (Fin n) 𝔸[K]) * Z) =
        (((y⁻¹ : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]) * ratMat ξ *
          (x : Matrix (Fin n) (Fin n) 𝔸[K])) * Z := by rw [Matrix.mul_assoc _ _ Z]
      _ = Z * (((y⁻¹ : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]) * ratMat ξ *
          (x : Matrix (Fin n) (Fin n) 𝔸[K])) := (hz _).symm
      _ = Z * ((y⁻¹ : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]) * ratMat ξ *
          (x : Matrix (Fin n) (Fin n) 𝔸[K]) := by simp only [Matrix.mul_assoc]
  simp only [harg] at h2 h3
  refine ⟨h1, h2, ?_⟩
  rw [h3, ← Complex.ofReal_mul, hdet]

end

end GroundTheory.Automorphic.GJGlobal
