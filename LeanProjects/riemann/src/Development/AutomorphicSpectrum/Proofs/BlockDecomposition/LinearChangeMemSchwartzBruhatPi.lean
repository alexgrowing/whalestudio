import Development.WeilBound.CoreStatements.AutomorphicKernels.EisensteinSeriesG2.HeisenbergTheta.HeisenbergThetaConstant.ThetaC
open NumberField Matrix MeasureTheory Filter Topology
open scoped NumberField.AdeleRing
open PositivityTheory.He2M1 GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.GJMatrix IdeleGroup PositivityTheory.RgEis

open scoped SchwartzMap Classical

set_option synthInstance.maxSize 1000

noncomputable section

namespace GlobalTheory.CompanionTheory.LinearChangeSchwartzBruhat

open GroundTheory.Automorphic.Adele2 NumberField.mixedEmbedding

variable {k : Type} [Field k] [NumberField k] {ι : Type} [Fintype ι] [DecidableEq ι]

def mulVecCLE (M : GL ι (mixedSpace k)) : (ι → mixedSpace k) ≃L[ℝ] (ι → mixedSpace k) :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := fun u ↦ (M : Matrix ι ι (mixedSpace k)) *ᵥ u
      invFun := fun u ↦ ((M⁻¹ : GL ι (mixedSpace k)) : Matrix ι ι (mixedSpace k)) *ᵥ u
      map_add' := fun u v ↦ mulVec_add _ u v
      map_smul' := fun c u ↦ mulVec_smul _ c u
      left_inv := fun u ↦ by
        simp only [mulVec_mulVec, Units.inv_mul, one_mulVec]
      right_inv := fun u ↦ by
        simp only [mulVec_mulVec, Units.mul_inv, one_mulVec] }

theorem mulVecCLE_apply (M : GL ι (mixedSpace k)) (u : ι → mixedSpace k) :
    mulVecCLE M u = (M : Matrix ι ι (mixedSpace k)) *ᵥ u := rfl

def mulVecHomeo (M : GL ι 𝔸ᶠ[k]) : (ι → 𝔸ᶠ[k]) ≃ₜ (ι → 𝔸ᶠ[k]) where
  toFun u := (M : Matrix ι ι 𝔸ᶠ[k]) *ᵥ u
  invFun u := ((M⁻¹ : GL ι 𝔸ᶠ[k]) : Matrix ι ι 𝔸ᶠ[k]) *ᵥ u
  left_inv u := by simp only [mulVec_mulVec, Units.inv_mul, one_mulVec]
  right_inv u := by simp only [mulVec_mulVec, Units.mul_inv, one_mulVec]
  continuous_toFun := Continuous.matrix_mulVec continuous_const continuous_id
  continuous_invFun := Continuous.matrix_mulVec continuous_const continuous_id

theorem comp_mulVec_mem_finiteSchwartzBruhatPi (M : GL ι 𝔸ᶠ[k]) {g : (ι → 𝔸ᶠ[k]) → ℂ}
    (hg : g ∈ finiteSchwartzBruhatPi k) :
    (fun z ↦ g ((M : Matrix ι ι 𝔸ᶠ[k]) *ᵥ z)) ∈ finiteSchwartzBruhatPi k := by
  obtain ⟨h1, h2⟩ := (mem_finiteSchwartzBruhatPi k).1 hg
  exact (mem_finiteSchwartzBruhatPi k).2
    ⟨h1.comp_continuous (mulVecHomeo M).continuous,
      h2.comp_isClosedEmbedding (mulVecHomeo M).isClosedEmbedding⟩

theorem infPartPi_mulVec (A : Matrix ι ι 𝔸[k]) (x : ι → 𝔸[k]) :
    infPartPi (A *ᵥ x) = A.map infRingHom *ᵥ infPartPi x := by
  funext i
  exact RingHom.map_mulVec infRingHom A x i

theorem finPartPi_mulVec (A : Matrix ι ι 𝔸[k]) (x : ι → 𝔸[k]) :
    finPartPi (A *ᵥ x) = A.map finRingHom *ᵥ finPartPi x := by
  funext i
  exact RingHom.map_mulVec finRingHom A x i

theorem ltr_schwartzBruhatTensorPi (A : GL ι 𝔸[k]) (φ : 𝓢(ι → mixedSpace k, ℂ))
    (g : (ι → 𝔸ᶠ[k]) → ℂ) :
    ltr A (schwartzBruhatTensorPi φ g) =
      schwartzBruhatTensorPi
        (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
          (mulVecCLE (Matrix.GeneralLinearGroup.map infRingHom A)) φ)
        (fun z ↦ g ((Matrix.GeneralLinearGroup.map finRingHom A : GL ι 𝔸ᶠ[k]) *ᵥ z)) := by
  funext x
  have h1 : ((Matrix.GeneralLinearGroup.map infRingHom A : GL ι (mixedSpace k)) :
      Matrix ι ι (mixedSpace k)) = (A : Matrix ι ι 𝔸[k]).map infRingHom := by
    refine Matrix.ext fun i j ↦ ?_
    rw [Matrix.GeneralLinearGroup.map_apply, Matrix.map_apply]
  have h2 : ((Matrix.GeneralLinearGroup.map finRingHom A : GL ι 𝔸ᶠ[k]) :
      Matrix ι ι 𝔸ᶠ[k]) = (A : Matrix ι ι 𝔸[k]).map finRingHom := by
    refine Matrix.ext fun i j ↦ ?_
    rw [Matrix.GeneralLinearGroup.map_apply, Matrix.map_apply]
  simp only [ltr, schwartzBruhatTensorPi, SchwartzMap.compCLMOfContinuousLinearEquiv_apply,
    Function.comp_apply, mulVecCLE_apply, h1, h2, infPartPi_mulVec, finPartPi_mulVec]

theorem ltr_mem {F : (ι → 𝔸[k]) → ℂ} (hF : F ∈ schwartzBruhatPi k ι) (A : GL ι 𝔸[k]) :
    ltr A F ∈ schwartzBruhatPi k ι := by
  induction hF using Submodule.span_induction with
  | mem G hG =>
    obtain ⟨φ, g, hg, rfl⟩ := hG
    rw [ltr_schwartzBruhatTensorPi]
    exact schwartzBruhatTensorPi_mem _ (comp_mulVec_mem_finiteSchwartzBruhatPi _ hg)
  | zero => exact zero_mem _
  | add G H _ _ ihG ihH => exact add_mem ihG ihH
  | smul a G _ ih => exact Submodule.smul_mem _ a ih

end GlobalTheory.CompanionTheory.LinearChangeSchwartzBruhat
