import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.Smooth
import GroundTheory.HeightsAndTheta.Theta.Weil.PartialFourierAdelicPi
import GroundTheory.HeightsAndTheta.Theta.AdelicFourierCoord

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2
open scoped Classical

noncomputable section

namespace UpperTheory.ConvolutionTheory.R2.D

variable {F : Type} [Field F] [NumberField F]

private theorem comp_signed_mem {ι κ : Type} [Fintype ι] [Fintype κ] (e : κ ≃ ι) (ε : κ → F)
    (hε : ∀ k, ε k * ε k = 1) {G : (κ → A F) → ℂ} (hG : G ∈ schwartzBruhatPi F κ) :
    (fun x : ι → A F => G fun k => rt (ε k) * x (e k)) ∈ schwartzBruhatPi F ι := by
  have hD : Matrix.diagonal ε * Matrix.diagonal ε = (1 : Matrix κ κ F) := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext k
    exact hε k
  let M : Matrix κ ι F := (Matrix.diagonal ε).submatrix id e.symm
  let N : Matrix ι κ F := (Matrix.diagonal ε).submatrix e.symm id
  have hNM : N * M = 1 := by
    have h := Matrix.submatrix_mul (Matrix.diagonal ε) (Matrix.diagonal ε) e.symm id e.symm
      Function.bijective_id
    rw [hD, Matrix.submatrix_one_equiv] at h
    exact h.symm
  have hMN : M * N = 1 := by
    have h := Matrix.submatrix_mul (Matrix.diagonal ε) (Matrix.diagonal ε) id e.symm id
      e.symm.bijective
    rw [hD, Matrix.submatrix_id_id] at h
    exact h.symm
  have h := GroundTheory.Heights₂.Theta.comp_mulVec_mem_schwartzBruhatPi M N hNM hMN hG
  have hx : ∀ x : ι → A F, (M.map (algebraMap F (A F)) *ᵥ x) = fun k => rt (ε k) * x (e k) := by
    intro x
    funext k
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, M, Matrix.submatrix_apply, id]
    rw [← e.sum_comp]
    simp only [Matrix.diagonal_apply]
    rw [Finset.sum_eq_single k]
    · simp
    · intro b _ hb
      simp [Ne.symm hb]
    · simp
  simpa only [hx] using h

private def eS : Fin 3 ⊕ Unit ≃ Fin 4 where
  toFun := Sum.elim ![0, 2, 3] fun _ => 1
  invFun := ![.inl 0, .inr (), .inl 1, .inl 2]
  left_inv := by
    rintro (i | ⟨⟩)
    · fin_cases i <;> rfl
    · rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

private def sg : Fin 3 ⊕ Unit → F := Sum.elim 1 fun _ => -1

private theorem sg_mul (k) : (sg k : F) * sg k = 1 := by
  rcases k with i | i <;> simp [sg]

private def FF (φ : V4 F → ℂ) (z : Fin 3 ⊕ Unit → A F) : ℂ := φ fun i => z (eS.symm i)

private theorem FF_mem {φ : V4 F → ℂ} (hφ : φ ∈ schwartzBruhatPi F (Fin 4)) :
    FF φ ∈ schwartzBruhatPi F (Fin 3 ⊕ Unit) := by
  have h := comp_signed_mem (F := F) eS.symm (fun _ => 1) (fun _ => by simp) hφ
  have he : FF φ = fun x => φ fun k => rt ((fun _ => 1 : Fin 4 → F) k) * x (eS.symm k) := by
    funext x
    simp [FF]
  rw [he]
  exact h

private theorem hat_eq (φ : V4 F → ℂ) (x : V4 F) :
    hat φ x = GroundTheory.Heights₂.Theta.partialFourierPi (FF φ) fun k => rt (sg k) * x (eS k) := by
  have hmp := measurePreserving_funUnique (adeleMeasure F) Unit
  have h := hmp.integral_comp' (g := fun s => φ (Function.update x 1 s) * ψ (-(s * x 1)))
  rw [hat, ← h, GroundTheory.Heights₂.Theta.partialFourierPi, adelicFourierPi, adeleMeasurePi]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  have h1 : Function.update x 1 (MeasurableEquiv.funUnique Unit (A F) y) =
      fun i => (Sum.elim (fun i => rt (sg (Sum.inl i)) * x (eS (Sum.inl i))) y
        : Fin 3 ⊕ Unit → A F) (eS.symm i) := by
    funext i
    fin_cases i <;> simp [eS, sg]
  have h2 : ψ (-(MeasurableEquiv.funUnique Unit (A F) y * x 1)) =
      ((adelicChar F (∑ i, y i * (rt (sg (Sum.inr i)) * x (eS (Sum.inr i)))) : Circle) : ℂ) := by
    simp [ψ, eS, sg]
  simp only [FF]
  rw [h1, h2]

private def tE {ι κ : Type} (e : κ ≃ ι) (ε : κ → F) (hε : ∀ k, ε k * ε k = 1) : (ι → F) ≃ (κ → F) where
  toFun ξ k := ε k * ξ (e k)
  invFun ξ i := ε (e.symm i) * ξ (e.symm i)
  left_inv ξ := by
    funext i
    simp [← mul_assoc, hε]
  right_inv ξ := by
    funext k
    simp [← mul_assoc, hε]

end UpperTheory.ConvolutionTheory.R2.D

end

theorem UpperTheory.ConvolutionTheory.R2.D.hatMem :
    ∀ (F : Type) [Field F] [NumberField F] (φ : S4 F), hat φ.1 ∈ schwartzBruhatPi F (Fin 4) ∧ Th φ.1 = Th (hat φ.1) := by
  intro F _ _ φ
  have hF := FF_mem φ.2
  constructor
  · have h := comp_signed_mem (F := F) eS sg sg_mul (GroundTheory.Heights₂.Theta.partialFourierPi_mem hF)
    have he : hat φ.1 = fun x => GroundTheory.Heights₂.Theta.partialFourierPi (FF φ.1) fun k => rt (sg k) * x (eS k) :=
      funext (hat_eq φ.1)
    rw [he]
    exact h
  · have hP := GroundTheory.Heights₂.Theta.tsum_partialFourierPi hF
    have h1 : Th φ.1 = ∑' ξ : Fin 3 ⊕ Unit → F, FF φ.1 fun s => algebraMap F (A F) (ξ s) := by
      rw [Th, ← (tE (F := F) eS (fun _ => 1) (fun _ => by simp)).tsum_eq]
      refine tsum_congr fun ξ => ?_
      simp [FF, tE]
    have h2 : Th (hat φ.1) = ∑' ξ : Fin 3 ⊕ Unit → F,
        GroundTheory.Heights₂.Theta.partialFourierPi (FF φ.1) fun s => algebraMap F (A F) (ξ s) := by
      rw [Th, ← (tE (F := F) eS sg sg_mul).tsum_eq]
      refine tsum_congr fun ξ => ?_
      rw [hat_eq]
      congr 1
      funext k
      simp [tE]
    rw [h1, h2, hP]
