import Mathlib
import GroundTheory.HeightsAndTheta.Theta.Weil.PartialFourierSchwartz
import GroundTheory.HeightsAndTheta.Theta.Weil.PartialFourierCoordinates

namespace GroundTheory.Heights₂.Theta

open GroundTheory.Global GroundTheory.Automorphic.GJMatrix NumberField NumberField.mixedEmbedding MeasureTheory
  Module
open scoped NumberField.AdeleRing SchwartzMap FourierTransform Classical

noncomputable section

set_option linter.unusedSectionVars false

variable {K : Type} [Field K] [NumberField K] {ι κ : Type} [Fintype ι] [Fintype κ]

variable (K ι κ) in

def toEuclidSplit : ((ι ⊕ κ) → mixedSpace K) ≃L[ℝ] (ι → mixedSpace K) × EuclidPi K κ :=
  (LinearEquiv.sumArrowLequivProdArrow ι κ ℝ (mixedSpace K)).toContinuousLinearEquiv.trans
    ((ContinuousLinearEquiv.refl ℝ (ι → mixedSpace K)).prodCongr (toEuclidPi K))

variable (K ι κ) in

def toEuclidSplitConj : ((ι ⊕ κ) → mixedSpace K) ≃L[ℝ] (ι → mixedSpace K) × EuclidPi K κ :=
  (LinearEquiv.sumArrowLequivProdArrow ι κ ℝ (mixedSpace K)).toContinuousLinearEquiv.trans
    ((ContinuousLinearEquiv.refl ℝ (ι → mixedSpace K)).prodCongr (toEuclidPiConj K))

theorem toEuclidSplitConj_apply (x : (ι ⊕ κ) → mixedSpace K) :
    toEuclidSplitConj K ι κ x = (fun i ↦ x (.inl i), toEuclidPiConj K fun k ↦ x (.inr k)) := rfl

theorem toEuclidSplit_symm_apply (a : ι → mixedSpace K) (v : EuclidPi K κ) :
    (toEuclidSplit K ι κ).symm (a, v) = Sum.elim a ((toEuclidPi K).symm v) := rfl

def mixedPartialFourier (φ : ((ι ⊕ κ) → mixedSpace K) → ℂ) (x : (ι ⊕ κ) → mixedSpace K) : ℂ :=
  mixedFourierPi K (fun u : κ → mixedSpace K ↦ φ (Sum.elim (fun i ↦ x (.inl i)) u))
    (fun k ↦ x (.inr k))

def mixedPartialFourierSchwartz (φ : 𝓢((ι ⊕ κ) → mixedSpace K, ℂ)) :
    𝓢((ι ⊕ κ) → mixedSpace K, ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (toEuclidSplitConj K ι κ)
    (partialFourierSndSchwartz
      (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (toEuclidSplit K ι κ).symm φ))

theorem mixedPartialFourierSchwartz_apply (φ : 𝓢((ι ⊕ κ) → mixedSpace K, ℂ)) :
    ⇑(mixedPartialFourierSchwartz φ) = mixedPartialFourier (φ : ((ι ⊕ κ) → mixedSpace K) → ℂ) := by
  funext x
  rw [mixedPartialFourier, mixedFourierPi_eq]
  rfl

def finitePartialFourier (g : ((ι ⊕ κ) → 𝔸ᶠ[K]) → ℂ) (x : (ι ⊕ κ) → 𝔸ᶠ[K]) : ℂ :=
  finiteFourierPi K (fun t : κ → 𝔸ᶠ[K] ↦ g (Sum.elim (fun i ↦ x (.inl i)) t)) (fun k ↦ x (.inr k))

theorem finitePartialFourier_finiteTensor (h : (ι ⊕ κ) → 𝔸ᶠ[K] → ℂ) :
    finitePartialFourier (finiteTensor h) =
      finiteTensor (Sum.elim (fun i ↦ h (.inl i)) fun k ↦ finiteFourier K (h (.inr k))) := by
  funext x
  have hsplit : (fun t : κ → 𝔸ᶠ[K] ↦ finiteTensor h (Sum.elim (fun i ↦ x (.inl i)) t)) =
      (∏ i, h (.inl i) (x (.inl i))) • finiteTensor fun k ↦ h (.inr k) := by
    funext t
    simp only [finiteTensor, Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Pi.smul_apply,
      smul_eq_mul]
  rw [finitePartialFourier, hsplit, finiteFourierPi_smul, finiteFourierPi_finiteTensor]
  simp only [finiteTensor, Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Pi.smul_apply,
    smul_eq_mul]

theorem finitePartialFourier_add {g₁ g₂ : ((ι ⊕ κ) → 𝔸ᶠ[K]) → ℂ}
    (h₁ : g₁ ∈ finiteSchwartzBruhatPi K) (h₂ : g₂ ∈ finiteSchwartzBruhatPi K) :
    finitePartialFourier (g₁ + g₂) = finitePartialFourier g₁ + finitePartialFourier g₂ := by
  funext x
  have e := finiteFourierPi_add
    (integrable_of_mem_finiteSchwartzBruhatPi (finiteSchwartzBruhatPi_sumElim_mem h₁ fun i ↦ x (.inl i)))
    (integrable_of_mem_finiteSchwartzBruhatPi (finiteSchwartzBruhatPi_sumElim_mem h₂ fun i ↦ x (.inl i)))
  exact congrFun e _

theorem finitePartialFourier_smul (c : ℂ) (g : ((ι ⊕ κ) → 𝔸ᶠ[K]) → ℂ) :
    finitePartialFourier (c • g) = c • finitePartialFourier g := by
  funext x
  exact congrFun (finiteFourierPi_smul (K := K) c _) _

theorem finitePartialFourier_mem {g : ((ι ⊕ κ) → 𝔸ᶠ[K]) → ℂ} (hg : g ∈ finiteSchwartzBruhatPi K) :
    finitePartialFourier g ∈ finiteSchwartzBruhatPi K := by
  have hsub := (finiteSchwartzBruhatPi_eq_span (K := K) (ι := ι ⊕ κ)).ge
  rw [finiteSchwartzBruhatPi_eq_span] at hg
  induction hg using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨⟨J, a⟩, rfl⟩ := hf
    rw [finitePartialFourier_finiteTensor]
    refine finiteTensor_mem fun s ↦ ?_
    cases s with
    | inl i => exact cosetIndicator_mem_finiteSchwartzBruhat J (a (.inl i))
    | inr k =>
      exact finiteFourier_mem_finiteSchwartzBruhat (cosetIndicator_mem_finiteSchwartzBruhat J _)
  | zero =>
    have : finitePartialFourier (0 : ((ι ⊕ κ) → 𝔸ᶠ[K]) → ℂ) = 0 := by
      simpa using finitePartialFourier_smul (K := K) (ι := ι) (κ := κ) 0 0
    rw [this]
    exact zero_mem _
  | add f₁ f₂ h₁ h₂ ih₁ ih₂ =>
    rw [finitePartialFourier_add (hsub h₁) (hsub h₂)]
    exact add_mem ih₁ ih₂
  | smul c f _ ih =>
    rw [finitePartialFourier_smul]
    exact Submodule.smul_mem _ c ih

def partialFourierPi (F : ((ι ⊕ κ) → 𝔸[K]) → ℂ) (z : (ι ⊕ κ) → 𝔸[K]) : ℂ :=
  adelicFourierPi K (fun y : κ → 𝔸[K] ↦ F (Sum.elim (fun i ↦ z (.inl i)) y)) (fun k ↦ z (.inr k))

theorem partialFourierPi_sumElim (F : ((ι ⊕ κ) → 𝔸[K]) → ℂ) (a : ι → 𝔸[K]) (η : κ → 𝔸[K]) :
    partialFourierPi F (Sum.elim a η) = adelicFourierPi K (fun y ↦ F (Sum.elim a y)) η := rfl

theorem partialFourierPi_schwartzBruhatTensorPi (φ : 𝓢((ι ⊕ κ) → mixedSpace K, ℂ))
    (g : ((ι ⊕ κ) → 𝔸ᶠ[K]) → ℂ) :
    partialFourierPi (schwartzBruhatTensorPi φ g) =
      schwartzBruhatTensorPi (mixedPartialFourierSchwartz φ) (finitePartialFourier g) := by
  funext z
  have hslice : (fun y : κ → 𝔸[K] ↦ schwartzBruhatTensorPi φ g (Sum.elim (fun i ↦ z (.inl i)) y)) =
      schwartzBruhatTensorPi (schwartzMapSliceSumElim (infPartPi fun i ↦ z (.inl i)) φ)
        (fun t ↦ g (Sum.elim (finPartPi fun i ↦ z (.inl i)) t)) := by
    funext y
    simp only [schwartzBruhatTensorPi, infPartPi_sumElim, finPartPi_sumElim,
      schwartzMapSliceSumElim_apply]
  rw [partialFourierPi, hslice, adelicFourierPi_schwartzBruhatTensorPi, schwartzBruhatTensorPi,
    schwartzBruhatTensorPi, mixedPartialFourierSchwartz_apply, mixedFourierPiSchwartz_apply]
  rfl

theorem integrable_partialFourierPi_slice {F : ((ι ⊕ κ) → 𝔸[K]) → ℂ}
    (hF : F ∈ schwartzBruhatPi K (ι ⊕ κ)) (a : ι → 𝔸[K]) :
    Integrable (fun y : κ → 𝔸[K] ↦ F (Sum.elim a y)) (adeleMeasurePi K) :=
  integrable_of_mem_schwartzBruhatPi (schwartzBruhatPi_sumElim_mem hF a)

theorem partialFourierPi_mem {F : ((ι ⊕ κ) → 𝔸[K]) → ℂ} (hF : F ∈ schwartzBruhatPi K (ι ⊕ κ)) :
    partialFourierPi F ∈ schwartzBruhatPi K (ι ⊕ κ) := by
  induction hF using Submodule.span_induction with
  | mem G hG =>
    obtain ⟨φ, g, hg, rfl⟩ := hG
    rw [partialFourierPi_schwartzBruhatTensorPi]
    exact schwartzBruhatTensorPi_mem _ (finitePartialFourier_mem hg)
  | zero =>
    have : partialFourierPi (0 : ((ι ⊕ κ) → 𝔸[K]) → ℂ) = 0 := by
      funext z
      simp [partialFourierPi, adelicFourierPi]
    rw [this]
    exact zero_mem _
  | add G H hG hH ihG ihH =>
    have : partialFourierPi (G + H) = partialFourierPi G + partialFourierPi H := by
      funext z
      exact congrFun (adelicFourierPi_add (integrable_partialFourierPi_slice hG _)
        (integrable_partialFourierPi_slice hH _)) _
    rw [this]
    exact add_mem ihG ihH
  | smul c G _ ih =>
    have : partialFourierPi (c • G) = c • partialFourierPi G := by
      funext z
      exact congrFun (adelicFourierPi_smul (K := K) c _) _
    rw [this]
    exact Submodule.smul_mem _ c ih

theorem algebraMap_sumElim (c : ι → K) (η : κ → K) :
    (fun s ↦ algebraMap K 𝔸[K] ((Sum.elim c η : (ι ⊕ κ) → K) s)) =
      Sum.elim (fun i ↦ algebraMap K 𝔸[K] (c i)) (fun k ↦ algebraMap K 𝔸[K] (η k)) := by
  funext s
  cases s <;> rfl

theorem tsum_sumElim {f : ((ι ⊕ κ) → K) → ℂ} (hf : Summable fun ξ ↦ ‖f ξ‖) :
    ∑' ξ, f ξ = ∑' c : ι → K, ∑' η : κ → K, f (Sum.elim c η) := by
  let e := Equiv.sumArrowEquivProdArrow ι κ K
  have h1 : Summable fun p : (ι → K) × (κ → K) ↦ f (e.symm p) :=
    (e.symm.summable_iff.mpr hf.of_norm)
  rw [← e.symm.tsum_eq, h1.tsum_prod' fun c ↦ h1.prod_factor c]
  rfl

theorem tsum_partialFourierPi {F : ((ι ⊕ κ) → 𝔸[K]) → ℂ} (hF : F ∈ schwartzBruhatPi K (ι ⊕ κ)) :
    ∑' ξ : (ι ⊕ κ) → K, partialFourierPi F (fun s ↦ algebraMap K 𝔸[K] (ξ s)) =
      ∑' ξ : (ι ⊕ κ) → K, F (fun s ↦ algebraMap K 𝔸[K] (ξ s)) := by
  rw [tsum_sumElim (poisson_of_mem_schwartzBruhatPi (partialFourierPi_mem hF)).1,
    tsum_sumElim (poisson_of_mem_schwartzBruhatPi hF).1]
  refine tsum_congr fun c ↦ ?_
  simp only [algebraMap_sumElim, partialFourierPi_sumElim]
  exact ((poisson_of_mem_schwartzBruhatPi
    (schwartzBruhatPi_sumElim_mem hF fun i ↦ algebraMap K 𝔸[K] (c i))).2.2).symm

end

end GroundTheory.Heights₂.Theta
