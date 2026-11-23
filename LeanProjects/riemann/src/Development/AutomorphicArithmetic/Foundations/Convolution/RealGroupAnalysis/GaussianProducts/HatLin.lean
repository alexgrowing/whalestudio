import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.ExistsRowSec
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaReindexing.HatMem

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.G
open scoped Classical ENNReal nonZeroDivisors

namespace UpperTheory.ConvolutionTheory.R2.G

variable {F : Type} [Field F] [NumberField F]

private def eQ : Fin 3 ⊕ Unit ≃ Fin 4 where
  toFun := Sum.elim ![0, 2, 3] fun _ => 1
  invFun := ![.inl 0, .inr (), .inl 1, .inl 2]
  left_inv := by
    rintro (i | ⟨⟩)
    · fin_cases i <;> rfl
    · rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

private theorem reindex_mem {φ : V4 F → ℂ} (hφ : φ ∈ schwartzBruhatPi F (Fin 4)) :
    (fun z : Fin 3 ⊕ Unit → A F => φ fun i => z (eQ.symm i)) ∈ schwartzBruhatPi F (Fin 3 ⊕ Unit) := by
  let M : Matrix (Fin 4) (Fin 3 ⊕ Unit) F := (1 : Matrix (Fin 4) (Fin 4) F).submatrix id eQ
  let N : Matrix (Fin 3 ⊕ Unit) (Fin 4) F := (1 : Matrix (Fin 4) (Fin 4) F).submatrix eQ id
  have hNM : N * M = 1 := by
    have h := Matrix.submatrix_mul (1 : Matrix (Fin 4) (Fin 4) F) (1 : Matrix (Fin 4) (Fin 4) F)
      eQ id eQ Function.bijective_id
    rw [Matrix.mul_one, Matrix.submatrix_one_equiv] at h
    exact h.symm
  have hMN : M * N = 1 := by
    have h := Matrix.submatrix_mul (1 : Matrix (Fin 4) (Fin 4) F) (1 : Matrix (Fin 4) (Fin 4) F)
      id eQ id eQ.bijective
    rw [Matrix.mul_one, Matrix.submatrix_id_id] at h
    exact h.symm
  have h := GroundTheory.Heights₂.Theta.comp_mulVec_mem_schwartzBruhatPi M N hNM hMN hφ
  have hx : ∀ x : Fin 3 ⊕ Unit → A F, (M.map (algebraMap F (A F)) *ᵥ x) = fun i => x (eQ.symm i) := by
    intro x
    funext i
    have hM : ∀ j k, M j k = if j = eQ k then (1 : F) else 0 := fun j k => by
      change (1 : Matrix (Fin 4) (Fin 4) F) j (eQ k) = _
      exact Matrix.one_apply
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, hM]
    rw [Finset.sum_eq_single (eQ.symm i)]
    · simp
    · intro b _ hb
      have : i ≠ eQ b := fun h => hb (by simp [h])
      simp [this]
    · simp
  simpa only [hx] using h

private theorem integrable_slice (φ : S4 F) (v : V4 F) :
    Integrable (fun s : A F => φ.1 (Function.update v 1 s)) (adeleMeasure F) := by
  have h := GroundTheory.Heights₂.Theta.integrable_partialFourierPi_slice (reindex_mem φ.2)
    (fun i : Fin 3 => v (eQ (.inl i)))
  have hmp := measurePreserving_funUnique (adeleMeasure F) Unit
  refine (hmp.integrable_comp_emb (MeasurableEquiv.measurableEmbedding _)).1 ?_
  refine h.congr (Eventually.of_forall fun y => ?_)
  have : (fun i => (Sum.elim (fun i : Fin 3 => v (eQ (.inl i))) y : Fin 3 ⊕ Unit → A F) (eQ.symm i)) =
      Function.update v 1 (MeasurableEquiv.funUnique Unit (A F) y) := by
    funext i
    fin_cases i <;> simp [eQ]
  simp only [Function.comp]
  rw [this]

private theorem integrable_term (φ : S4 F) (v : V4 F) :
    Integrable (fun s : A F => φ.1 (Function.update v 1 s) * ψ (-(s * v 1))) (adeleMeasure F) := by
  have hs := integrable_slice φ v
  have hc : Continuous fun s : A F => ψ (-(s * v 1)) :=
    continuous_subtype_val.comp ((continuous_adelicChar (K := F)).comp
      (continuous_id.mul continuous_const).neg)
  exact hs.mono (hs.1.mul hc.aestronglyMeasurable)
    (Eventually.of_forall fun s => by rw [norm_mul, ψ, Circle.norm_coe, mul_one])

end UpperTheory.ConvolutionTheory.R2.G

theorem UpperTheory.ConvolutionTheory.R2.G.hatLin :
    ∀ (F : Type) [Field F] [NumberField F], ∃ H : S4 F →ₗ[ℂ] S4 F, ∀ φ, (H φ).1 = hat φ.1 := by
  intro F _ _
  have hadd : ∀ φ χ : S4 F, hat (φ + χ).1 = hat φ.1 + hat χ.1 := by
    intro φ χ
    funext v
    simp only [hat, Submodule.coe_add, Pi.add_apply, add_mul]
    exact integral_add (integrable_term φ v) (integrable_term χ v)
  have hsmul : ∀ (c : ℂ) (φ : S4 F), hat (c • φ).1 = c • hat φ.1 := by
    intro c φ
    funext v
    simp only [hat, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, mul_assoc]
    exact integral_const_mul c _
  refine ⟨{ toFun := fun φ => ⟨hat φ.1, (UpperTheory.ConvolutionTheory.R2.D.hatMem F φ).1⟩
            map_add' := fun φ χ => Subtype.ext (hadd φ χ)
            map_smul' := fun c φ => Subtype.ext (hsmul c φ) }, fun φ => rfl⟩
