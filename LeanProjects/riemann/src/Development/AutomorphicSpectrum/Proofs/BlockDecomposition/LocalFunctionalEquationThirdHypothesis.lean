import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.LocalWhittakerDuality.WhittakerFunctionalEquationAdditive
import GroundTheory.HeightsAndTheta.Theta.WeilBox
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BigCellKernelBoundedSupport
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PureTensorDecompositionLocal
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData GroundTheory.Heights₂.Theta
open scoped ValuativeRel

noncomputable section

namespace GlobalTheory.CompanionTheory.PureTensorFourier

open GlobalTheory.CompanionTheory.BigCell.PhdSupp

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]

def mat (X : Fin 2 × Fin 2 → F) : Matrix (Fin 2) (Fin 2) F := Matrix.of fun i j => X (i, j)

theorem mem_pi_of_mem {f : (Fin 2 → F) → ℂ} (h : f ∈ GodementSectionLocal.schwartzBruhat2 F) :
    f ∈ schwartzBruhatPi F (Fin 2) :=
  ⟨h.1, h.2⟩

theorem pFT_eq_sum (ψ : AddChar F Circle) (hψ : Continuous ψ)
    (Φ : Matrix (Fin 2) (Fin 3) F → ℂ) {n : ℕ} (Φ₁ : Fin n → Matrix (Fin 2) (Fin 2) F → ℂ)
    (Φ₂ : Fin n → (Fin 2 → F) → ℂ) (h₂ : ∀ i, Φ₂ i ∈ GodementSectionLocal.schwartzBruhat2 F)
    (hΦ : ∀ A y, Φ (cat3 A y) = ∑ i, Φ₁ i A * Φ₂ i y)
    (A : Matrix (Fin 2) (Fin 2) F) (ξ : Fin 2 → F) :
    pFT ψ Φ A ξ = ∑ i, Φ₁ i A * fourierPi ψ (Φ₂ i) (-ξ) := by
  have hint : ∀ i, Integrable (fun y => Φ₁ i A * (Φ₂ i y * (ψ (y ⬝ᵥ (-ξ)) : ℂ))) (selfDualPi (Fin 2) ψ) :=
    fun i => (integrable_mul_char_of_mem_schwartzBruhatPi hψ (mem_pi_of_mem (h₂ i)) (-ξ)).const_mul _
  have hpt : ∀ y : Fin 2 → F, Φ (cat3 A y) * (ψ (-(ξ 0 * y 0 + ξ 1 * y 1)) : ℂ) =
      ∑ i, Φ₁ i A * (Φ₂ i y * (ψ (y ⬝ᵥ (-ξ)) : ℂ)) := by
    intro y
    have hd : y ⬝ᵥ (-ξ) = -(ξ 0 * y 0 + ξ 1 * y 1) := by
      simp [dotProduct, Fin.sum_univ_two]
      ring
    rw [hΦ, Finset.sum_mul, hd]
    exact Finset.sum_congr rfl fun i _ => by ring
  change ∫ y, Φ (cat3 A y) * (ψ (-(ξ 0 * y 0 + ξ 1 * y 1)) : ℂ) ∂selfDualPi (Fin 2) ψ = _
  simp_rw [hpt]
  rw [integral_finsetSum _ fun i _ => hint i]
  exact Finset.sum_congr rfl fun i _ => integral_const_mul _ _

theorem a3 : A3 := by
  intro F _ _ _ _ _ _ ψ hψ n Φ Φ₁ Φ₂ h₁ h₂ hΦ
  refine ⟨fun A ξ => ?_, fun A ξ => ?_⟩
  · rw [pFT_eq_sum ψ hψ.1 Φ Φ₁ Φ₂ h₂ hΦ A ξ]
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    change ∫ x, Φ₂ i x * (ψ (x ⬝ᵥ (-ξ)) : ℂ) ∂selfDualPi (Fin 2) ψ =
      ∫ x, Φ₂ i x * (ψ (-(x 0 * ξ 0 + x 1 * ξ 1)) : ℂ) ∂selfDualPi (Fin 2) ψ
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    have hd : x ⬝ᵥ (-ξ) = -(x 0 * ξ 0 + x 1 * ξ 1) := by
      simp [dotProduct, Fin.sum_univ_two]
    simp only [hd]
  · have hdot : ∀ X : Fin 2 × Fin 2 → F,
        X ⬝ᵥ (fun p : Fin 2 × Fin 2 => A p.1 p.2) = ∑ i, ∑ j, X (i, j) * A i j := by
      intro X
      simp only [dotProduct]
      exact Fintype.sum_prod_type _
    have hint : ∀ i, Integrable (fun X : Fin 2 × Fin 2 → F =>
        Φ₁ i (Matrix.of fun a b => X (a, b)) * (ψ (∑ a, ∑ b, X (a, b) * A a b) : ℂ) * Φ₂ i (-ξ))
        (Measure.pi fun _ => selfDualMeasure ψ) := by
      intro i
      have h := integrable_mul_char_of_mem_schwartzBruhatPi hψ.1 (flat_mem (h₁ i))
        (fun p : Fin 2 × Fin 2 => A p.1 p.2)
      simp only [hdot] at h
      exact h.mul_const _
    have hpt : ∀ X : Fin 2 × Fin 2 → F,
        Φ (cat3 (Matrix.of fun a b => X (a, b)) (-ξ)) * (ψ (∑ a, ∑ b, X (a, b) * A a b) : ℂ) =
        ∑ i, Φ₁ i (Matrix.of fun a b => X (a, b)) * (ψ (∑ a, ∑ b, X (a, b) * A a b) : ℂ) *
          Φ₂ i (-ξ) := by
      intro X
      rw [hΦ, Finset.sum_mul]
      exact Finset.sum_congr rfl fun i _ => by ring
    unfold dFT matrixFourierTransposeInv
    simp_rw [hpt]
    rw [integral_finsetSum _ fun i _ => hint i]
    exact Finset.sum_congr rfl fun i _ => integral_mul_const _ _

end GlobalTheory.CompanionTheory.PureTensorFourier
