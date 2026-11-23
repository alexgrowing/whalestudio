import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.WaveSt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsMultOfFintype

noncomputable section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC
open GlobalTheory.CompanionTheory.WaveMult

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.WaveMult

variable {n : ℕ}

theorem isOpen_GLs_dens (n : ℕ) : IsOpen (GLs n) := by
  have h : Continuous fun g : Mat n => g.det := continuous_id.matrix_det
  exact isOpen_ne.preimage h

theorem mul_unitary_mem_GLs {y : Mat n} (hy : y ∈ GLs n) (k : Matrix.unitaryGroup (Fin n) ℂ) :
    y * k.1 ∈ GLs n := by
  have h1 : k.1 * star k.1 = 1 := Matrix.mem_unitaryGroup_iff.1 k.2
  have h2 : k.1.det ≠ 0 := Matrix.det_ne_zero_of_right_inverse h1
  have h3 : y.det ≠ 0 := hy
  change (y * k.1).det ≠ 0
  rw [Matrix.det_mul]
  exact mul_ne_zero h3 h2

theorem inner_rho_inv (E : KMod n) (k : Matrix.unitaryGroup (Fin n) ℂ) (a v : E.V) :
    ⟪E.ρ k⁻¹ a, v⟫_ℂ = ⟪a, E.ρ k v⟫_ℂ := by
  let L : E.V →ₗᵢ[ℂ] E.V := ⟨(E.ρ k : E.V →ₗ[ℂ] E.V), E.iso k⟩
  have h1 : E.ρ k (E.ρ k⁻¹ a) = a := by
    have : (E.ρ k * E.ρ k⁻¹) a = a := by
      rw [← map_mul, mul_inv_cancel, map_one]; rfl
    simpa using this
  have h2 := L.inner_map_map (E.ρ k⁻¹ a) v
  have h3 : L (E.ρ k⁻¹ a) = a := h1
  have h4 : L v = E.ρ k v := rfl
  rw [h3, h4] at h2
  exact h2.symm

theorem section_orth_cpt_zero : KerUniq → ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n))
    [μ.IsHaarMeasure] (E : KMod n) (A : Mat n → E.V), ContinuousOn A (GLs n) →
    (∀ y ∈ GLs n, ∀ k₂ : Matrix.unitaryGroup (Fin n) ℂ, A (y * k₂.1) = E.ρ k₂⁻¹ (A y)) →
    (∀ h ∈ CE E, Cpt h → ∫ y : G n, ⟪A y.val, h y.val⟫_ℂ ∂μ = 0) → ∀ y ∈ GLs n, A y = 0 := by
  intro hK n _ _ μ _ E A hA hEq hOrth y hy
  haveI : CompleteSpace E.V := FiniteDimensional.complete ℂ E.V
  let e : E.V := A y
  let κ : Mat n → (E.V →L[ℂ] E.V) := fun z => (innerSL ℂ (A z)).smulRight e
  have hκ : ∀ z v, κ z v = ⟪A z, v⟫_ℂ • e := fun z v => by simp [κ]
  have hcont : ContinuousOn κ (GLs n) := by
    have h1 : Continuous fun a : E.V => (innerSL ℂ a).smulRight e :=
      ((ContinuousLinearMap.smulRightL ℂ E.V E.V).flip e).continuous.comp (innerSL ℂ).continuous
    exact h1.comp_continuousOn hA
  have hequi : ∀ z ∈ GLs n, ∀ k₂ : Matrix.unitaryGroup (Fin n) ℂ, κ (z * k₂.1) = κ z * E.ρ k₂ := by
    intro z hz k₂
    ext v
    rw [ContinuousLinearMap.mul_apply, hκ, hκ, hEq z hz k₂, inner_rho_inv]
  have hact : ∀ f ∈ CE E, Cpt f → (∀ z ∈ GLs n, z ∉ GLs n → f z = 0) → act μ E κ f 1 = 0 := by
    intro f hf hc _
    have h0 := hOrth f hf hc
    unfold act
    simp only [one_mul, hκ]
    rw [integral_smul_const, h0, zero_smul]
  have hz := hK n μ E κ (GLs n) (isOpen_GLs_dens n) subset_rfl
    (fun z hz k => mul_unitary_mem_GLs hz k) hcont hequi hact y hy
  have h1 : ⟪A y, A y⟫_ℂ • e = 0 := by
    rw [← hκ, hz]; rfl
  rcases smul_eq_zero.1 h1 with h | h
  · exact inner_self_eq_zero.1 h
  · exact h

end GlobalTheory.CompanionTheory.WaveMult
