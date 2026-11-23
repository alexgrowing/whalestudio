import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.LocalWhittakerDuality.WhittakerFunctionalEquationAdditive
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Th
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Gauge
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IwasawaHaarMeasureDecomposition
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData GlobalTheory.CompanionTheory.DampedZetaMajorant GlobalTheory.CompanionTheory.GL2ZetaUnfolding
open scoped ValuativeRel

noncomputable section

namespace GlobalTheory.CompanionTheory.IwaRinv

section Loc

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]

attribute [local instance] GlobalTheory.CompanionTheory.IwaHaar.secondCountable_units GlobalTheory.CompanionTheory.LocalTestVectors.secondCountable_GL2
  GlobalTheory.CompanionTheory.IwaHaar.haar_inst GlobalTheory.CompanionTheory.IwaHaar.right_inst

open Classical in

def secX (h : GL (Fin 2) F) : F :=
  if h.val 1 1 = 0 then h.val 0 0 / h.val 1 0 else h.val 0 1 / h.val 1 1

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] in
theorem entry_ne_zero (h : GL (Fin 2) F) (h1 : h.val 1 1 = 0) : h.val 1 0 ≠ 0 := by
  intro h0
  have hd : (h.val).det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det _).1 h.isUnit).ne_zero
  rw [Matrix.det_fin_two, h1, h0] at hd
  simp at hd

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] in
theorem bruhatCoordinate_unipotent_mul (y : F) (h : GL (Fin 2) F) : secX (uni2 y * h) = secX h + y := by
  have e00 : (uni2 y * h).val 0 0 = h.val 0 0 + y * h.val 1 0 := by
    simp [uni2, Matrix.mul_apply, Fin.sum_univ_two]
  have e01 : (uni2 y * h).val 0 1 = h.val 0 1 + y * h.val 1 1 := by
    simp [uni2, Matrix.mul_apply, Fin.sum_univ_two]
  have e10 : (uni2 y * h).val 1 0 = h.val 1 0 := by
    simp [uni2, Matrix.mul_apply, Fin.sum_univ_two]
  have e11 : (uni2 y * h).val 1 1 = h.val 1 1 := by
    simp [uni2, Matrix.mul_apply, Fin.sum_univ_two]
  unfold secX
  rw [e00, e01, e10, e11]
  by_cases h1 : h.val 1 1 = 0
  · have h0 := entry_ne_zero h h1
    rw [if_pos h1, if_pos h1]
    field_simp
  · rw [if_neg h1, if_neg h1]
    field_simp

omit [ValuativeRel F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] in
theorem continuous_entry (i j : Fin 2) :
    Continuous fun h : GL (Fin 2) F => h.val i j :=
  (show Continuous fun A : Matrix (Fin 2) (Fin 2) F => A i j from
    continuous_id.matrix_elem i j).comp Units.continuous_val

theorem measurable_secX : Measurable (secX (F := F)) := by
  have m : ∀ i j : Fin 2, Measurable fun h : GL (Fin 2) F => h.val i j :=
    fun i j => (continuous_entry i j).measurable
  unfold secX
  exact Measurable.ite ((m 1 1) (measurableSet_singleton 0)) ((m 0 0).div (m 1 0)) ((m 0 1).div (m 1 1))

def beta (ψ : AddChar F Circle) (h : GL (Fin 2) F) : ENNReal :=
  (𝒪[F] : Set F).indicator (fun _ => (selfDualMeasure ψ (𝒪[F] : Set F))⁻¹) (secX h)

theorem measurableSet_integers : MeasurableSet (𝒪[F] : Set F) := by
  have e : (𝒪[F] : Set F) = uni2 ⁻¹' (GLnLocal.integralGL F 2 : Set (GL (Fin 2) F)) := by
    ext x
    exact (GlobalTheory.CompanionTheory.IwaHaar.unipotent_mem_integral_GL_iff x).symm
  rw [e]
  exact GlobalTheory.CompanionTheory.IwaHaar.continuous_unipotentGL2.measurable (GLnLocal.isOpen_integralGL F 2).measurableSet

theorem measurable_beta (ψ : AddChar F Circle) : Measurable (beta ψ) :=
  (measurable_const.indicator measurableSet_integers).comp measurable_secX

theorem lintegral_beta (ψ : AddChar F Circle) (h : GL (Fin 2) F) :
    ∫⁻ y, beta ψ (uni2 y * h) ∂selfDualMeasure ψ = 1 := by
  have hO : selfDualMeasure ψ (𝒪[F] : Set F) ≠ 0 := by
    rw [selfDualMeasure_integers]
    exact ENNReal.coe_ne_zero.2 (selfDualMeasure_coeff_ne_zero ψ)
  have hT : selfDualMeasure ψ (𝒪[F] : Set F) ≠ ⊤ := by
    rw [selfDualMeasure_integers]
    exact ENNReal.coe_ne_top
  simp only [beta, bruhatCoordinate_unipotent_mul]
  rw [lintegral_add_left_eq_self
    ((𝒪[F] : Set F).indicator fun _ => (selfDualMeasure ψ (𝒪[F] : Set F))⁻¹) (secX h),
    lintegral_indicator_const measurableSet_integers]
  exact ENNReal.inv_mul_cancel hO hT

end Loc

end GlobalTheory.CompanionTheory.IwaRinv

open GlobalTheory.CompanionTheory.IwaRinv in

theorem GlobalTheory.CompanionTheory.IwaRinv.main : ForS fun F _ _ _ _ _ _ ψ => ∀ (f : GL (Fin 2) F → ENNReal), Measurable f → (∀ x h, f (uni2 x * h) = f h) →
  ∀ g : GL (Fin 2) F, ∫⁻ p, ENNReal.ofReal (wR p) * f (hI p * g) ∂mIw ψ = ∫⁻ p, ENNReal.ofReal (wR p) * f (hI p) ∂mIw ψ := by
  intro F _ _ _ _ _ _ ψ hψ f hf hN g
  haveI := GlobalTheory.CompanionTheory.IwaHaar.haar_inst ψ
  haveI := GlobalTheory.CompanionTheory.IwaHaar.right_inst ψ
  haveI : SecondCountableTopology (GL (Fin 2) F) := GlobalTheory.CompanionTheory.LocalTestVectors.secondCountable_GL2
  obtain ⟨c, -, -, hc⟩ := GlobalTheory.CompanionTheory.IwaHaar.main F ψ hψ
  have key : ∀ (φ : GL (Fin 2) F → ENNReal), Measurable φ → (∀ x h, φ (uni2 x * h) = φ h) →
      ∀ β : GL (Fin 2) F → ENNReal, Measurable β →
        (∀ h, ∫⁻ y, β (uni2 y * h) ∂selfDualMeasure ψ = 1) →
        ∫⁻ p, ENNReal.ofReal (wR p) * φ (hI p) ∂mIw ψ = c * ∫⁻ h, φ h * β h ∂LFS.hG ψ := by
    intro φ hφ hφN β hβ hβ1
    rw [← hc (fun h => φ h * β h) (hφ.mul hβ)]
    refine lintegral_congr fun p => ?_
    have hm : Measurable fun x : F => β (uni2 x * hI p) :=
      hβ.comp (GlobalTheory.CompanionTheory.IwaHaar.continuous_unipotentGL2.measurable.mul_const _)
    simp only [hφN, ← mul_assoc]
    rw [lintegral_const_mul _ hm, hβ1, mul_one]
  have h1 := key (fun h => f (h * g)) (hf.comp (measurable_mul_const g))
    (fun x h => by simp only [mul_assoc, hN]) (beta ψ) (measurable_beta ψ) (lintegral_beta ψ)
  have h2 := key f hf hN (fun h => beta ψ (h * g⁻¹))
    ((measurable_beta ψ).comp (measurable_mul_const g⁻¹))
    (fun h => by simp only [mul_assoc]; exact lintegral_beta ψ (h * g⁻¹))
  have h3 := lintegral_mul_right_eq_self (μ := LFS.hG ψ)
    (fun h => f h * beta ψ (h * g⁻¹)) g
  simp only [mul_inv_cancel_right] at h3
  rw [h1, h2, h3]
