import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.NApply
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.ChirpQ
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.FtBasic
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaReindexing.MapMulInvEqOne

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.C

noncomputable section

private theorem continuous_form {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    (a c b d e : R) :
    Continuous fun y : Fin 4 → R => 2 * (y 2 * a - c * (y 3 * b)) - y 1 * d - y 0 * e := by
  fun_prop

namespace UpperTheory.ConvolutionTheory.R2.C

variable {F : Type} [Field F] [NumberField F]

private theorem continuous_psi : Continuous (ψ : A F → ℂ) :=
  continuous_subtype_val.comp (continuous_adelicChar (K := F))

private theorem norm_psi (x : A F) : ‖ψ x‖ = 1 := Circle.norm_coe _

private theorem continuous_quaternaryForm_left (δ : F) (v : V4 F) : Continuous fun y : V4 F => B4 δ y v := by
  exact continuous_form (v 2) (rt δ) (v 3) (v 0) (v 1)

private theorem integrable_ft (δ : F) {φ : V4 F → ℂ} (hφ : φ ∈ schwartzBruhatPi F (Fin 4)) (v : V4 F) :
    Integrable (fun y => φ y * ψ (B4 δ y v)) (adeleMeasurePi F) := by
  refine (integrable_of_mem_schwartzBruhatPi hφ).mul_bdd (c := 1) ?_ ?_
  · exact (continuous_psi.comp (continuous_quaternaryForm_left δ v)).aestronglyMeasurable
  · exact Eventually.of_forall fun y => (norm_psi _).le

private theorem quaternaryFourier_add (δ : F) {φ φ' : V4 F → ℂ} (hφ : φ ∈ schwartzBruhatPi F (Fin 4))
    (hφ' : φ' ∈ schwartzBruhatPi F (Fin 4)) (v : V4 F) :
    ft4 δ (φ + φ') v = ft4 δ φ v + ft4 δ φ' v := by
  unfold ft4
  rw [← integral_add (integrable_ft δ hφ v) (integrable_ft δ hφ' v)]
  congr 1
  funext y
  simp only [Pi.add_apply, add_mul]

private theorem quaternaryFourier_smul (δ : F) (c : ℂ) (φ : V4 F → ℂ) (v : V4 F) :
    ft4 δ (c • φ) v = c * ft4 δ φ v := by
  unfold ft4
  rw [← integral_const_mul]
  congr 1
  funext y
  simp only [Pi.smul_apply, smul_eq_mul, mul_assoc]

private def opN (δ : F) (b : A F) : Module.End ℂ (S4 F) where
  toFun φ := ⟨fun v => ψ (b * q4 δ v) * φ.1 v, by
    have h := chirpQ F δ b 0 φ.1 φ.2
    have e : (fun v => ψ (b * q4 δ v + B4 δ v 0) * φ.1 v) = fun v => ψ (b * q4 δ v) * φ.1 v := by
      funext v
      simp [B4]
    rwa [e] at h⟩
  map_add' φ φ' := by
    ext v
    simp [mul_add]
  map_smul' c φ := by
    ext v
    simp only [RingHom.id_apply, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul]
    ring

private def scal (a : (A F)ˣ) : GL (Fin 4) (A F) :=
  ⟨(a : A F) • 1, ((a⁻¹ : (A F)ˣ) : A F) • 1, by simp [smul_smul], by simp [smul_smul]⟩

private def opM (η : (A F)ˣ →* ℂˣ) (a : (A F)ˣ) : Module.End ℂ (S4 F) where
  toFun φ := ⟨fun v => ((η a : ℂˣ) : ℂ) * ((ab a ^ 2 : ℝ) : ℂ) * φ.1 fun i => (a : A F) * v i, by
    have h := D.sClos F (Fin 4) (scal a) φ.1 φ.2
    have e : (fun v => φ.1 ((scal a).val *ᵥ v)) = fun v => φ.1 fun i => (a : A F) * v i := by
      funext v
      have e' : (scal a).val *ᵥ v = fun i => (a : A F) * v i := by
        funext i
        simp [scal, Matrix.smul_mulVec]
      rw [e']
    rw [e] at h
    exact Submodule.smul_mem _ (((η a : ℂˣ) : ℂ) * ((ab a ^ 2 : ℝ) : ℂ)) h⟩
  map_add' φ φ' := by
    ext v
    simp [mul_add]
  map_smul' c φ := by
    ext v
    simp only [RingHom.id_apply, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul]
    ring

private def opW (δ : F) (hδ : δ ≠ 0) : Module.End ℂ (S4 F) where
  toFun φ := ⟨ft4 δ φ.1, (ftBasic F δ hδ φ.1 φ.2).1⟩
  map_add' φ φ' := by
    ext v
    exact quaternaryFourier_add δ φ.2 φ'.2 v
  map_smul' c φ := by
    ext v
    exact quaternaryFourier_smul δ c φ.1 v

end UpperTheory.ConvolutionTheory.R2.C

end

theorem UpperTheory.ConvolutionTheory.R2.C.opsEx :
    ∀ (F : Type) [Field F] [NumberField F] (δ : F) (η : (A F)ˣ →* ℂˣ), δ ≠ 0 → Nonempty (Ops δ η) := by
  intro F _ _ δ η hδ
  exact ⟨{ N := opN δ, M := opM η, W := opW δ hδ
           N_apply := fun _ _ _ => rfl
           M_apply := fun _ _ _ => rfl
           W_apply := fun _ _ => rfl }⟩
