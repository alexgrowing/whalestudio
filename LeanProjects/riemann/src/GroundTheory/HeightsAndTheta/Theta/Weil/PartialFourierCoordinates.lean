import Mathlib
import GroundTheory.HeightsAndTheta.Theta.Weil.PartialFourierTheta
import GroundTheory.HeightsAndTheta.Theta.AdelicFourier

namespace GroundTheory.Heights₂.Theta

open GroundTheory.Global GroundTheory.Automorphic.GJMatrix NumberField NumberField.mixedEmbedding MeasureTheory
  TensorProduct Module
open scoped NumberField.AdeleRing SchwartzMap

noncomputable section

set_option linter.unusedSectionVars false

section Slice

open scoped Classical

variable {K : Type*} [Field K] [NumberField K]
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

private def sliceInl : (κ → mixedSpace K) →L[ℝ] ((ι ⊕ κ) → mixedSpace K) :=
  ContinuousLinearMap.pi fun s ↦
    Sum.elim (fun _ ↦ (0 : (κ → mixedSpace K) →L[ℝ] mixedSpace K))
      (fun j ↦ ContinuousLinearMap.proj j) s

private theorem sliceInl_apply (u : κ → mixedSpace K) :
    (sliceInl (ι := ι) u : (ι ⊕ κ) → mixedSpace K) = Sum.elim (0 : ι → mixedSpace K) u := by
  funext s
  cases s <;> rfl

private theorem sumElim_hasTemperateGrowth (c : ι → mixedSpace K) :
    (fun u : κ → mixedSpace K ↦ (Sum.elim c u : (ι ⊕ κ) → mixedSpace K)).HasTemperateGrowth := by
  have h : (fun u : κ → mixedSpace K ↦ (Sum.elim c u : (ι ⊕ κ) → mixedSpace K)) =
      fun u ↦ sliceInl (ι := ι) u + Sum.elim c 0 := by
    funext u s
    rw [sliceInl_apply]
    cases s <;> simp
  rw [h]
  exact (sliceInl (K := K) (ι := ι) (κ := κ)).hasTemperateGrowth.add
    (Function.HasTemperateGrowth.const _)

private theorem sumElim_upper (c : ι → mixedSpace K) :
    ∃ (k : ℕ) (C : ℝ), ∀ u : κ → mixedSpace K,
      ‖u‖ ≤ C * (1 + ‖(Sum.elim c u : (ι ⊕ κ) → mixedSpace K)‖) ^ k := by
  refine ⟨1, 1, fun u ↦ ?_⟩
  have hle : ‖u‖ ≤ ‖(Sum.elim c u : (ι ⊕ κ) → mixedSpace K)‖ :=
    (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun j ↦ by
      simpa using norm_le_pi_norm (Sum.elim c u : (ι ⊕ κ) → mixedSpace K) (Sum.inr j)
  rw [pow_one, one_mul]
  linarith

def schwartzMapSliceSumElim (c : ι → mixedSpace K) (φ : 𝓢((ι ⊕ κ) → mixedSpace K, ℂ)) :
    𝓢(κ → mixedSpace K, ℂ) :=
  SchwartzMap.compCLM ℝ (sumElim_hasTemperateGrowth c) (sumElim_upper c) φ

theorem schwartzMapSliceSumElim_apply (c : ι → mixedSpace K) (φ : 𝓢((ι ⊕ κ) → mixedSpace K, ℂ))
    (u : κ → mixedSpace K) : schwartzMapSliceSumElim c φ u = φ (Sum.elim c u) := rfl

theorem finiteSchwartzBruhatPi_sumElim_mem {g : ((ι ⊕ κ) → 𝔸ᶠ[K]) → ℂ} (hg : g ∈ finiteSchwartzBruhatPi K)
    (c : ι → 𝔸ᶠ[K]) : (fun v : κ → 𝔸ᶠ[K] ↦ g (Sum.elim c v)) ∈ finiteSchwartzBruhatPi K := by
  rw [mem_finiteSchwartzBruhatPi] at hg ⊢
  obtain ⟨hl, hc⟩ := hg
  have hcont : Continuous fun v : κ → 𝔸ᶠ[K] ↦ (Sum.elim c v : (ι ⊕ κ) → 𝔸ᶠ[K]) :=
    continuous_pi fun s ↦ by
      cases s with
      | inl i => exact continuous_const
      | inr j => exact continuous_apply j
  refine ⟨hl.comp_continuous hcont, ?_⟩
  have hπ : Continuous fun w : (ι ⊕ κ) → 𝔸ᶠ[K] ↦ w ∘ Sum.inr :=
    continuous_pi fun j ↦ continuous_apply (Sum.inr j)
  refine HasCompactSupport.intro (hc.image hπ) fun v hv ↦ ?_
  by_contra h
  exact hv ⟨Sum.elim c v, subset_tsupport _ h, Sum.elim_comp_inr c v⟩

theorem infPartPi_sumElim (a : ι → 𝔸[K]) (x : κ → 𝔸[K]) :
    infPartPi (Sum.elim a x : (ι ⊕ κ) → 𝔸[K]) = Sum.elim (infPartPi a) (infPartPi x) := by
  funext s
  cases s <;> rfl

theorem finPartPi_sumElim (a : ι → 𝔸[K]) (x : κ → 𝔸[K]) :
    finPartPi (Sum.elim a x : (ι ⊕ κ) → 𝔸[K]) = Sum.elim (finPartPi a) (finPartPi x) := by
  funext s
  cases s <;> rfl

theorem schwartzBruhatPi_sumElim_mem {F : ((ι ⊕ κ) → 𝔸[K]) → ℂ}
    (hF : F ∈ schwartzBruhatPi K (ι ⊕ κ)) (a : ι → 𝔸[K]) :
    (fun x : κ → 𝔸[K] ↦ F (Sum.elim a x)) ∈ schwartzBruhatPi K κ := by
  induction hF using Submodule.span_induction with
  | mem G hG =>
    obtain ⟨φ, g, hg, rfl⟩ := hG
    have h : (fun x : κ → 𝔸[K] ↦ schwartzBruhatTensorPi φ g (Sum.elim a x)) =
        schwartzBruhatTensorPi (schwartzMapSliceSumElim (infPartPi a) φ)
          (fun v ↦ g (Sum.elim (finPartPi a) v)) := by
      funext x
      simp only [schwartzBruhatTensorPi, schwartzMapSliceSumElim_apply, infPartPi_sumElim,
        finPartPi_sumElim]
    rw [h]
    exact schwartzBruhatTensorPi_mem _ (finiteSchwartzBruhatPi_sumElim_mem hg _)
  | zero => exact zero_mem _
  | add F G _ _ hF hG => exact add_mem hF hG
  | smul c F _ hF => exact Submodule.smul_mem _ c hF

end Slice

section Pairing

variable {K W P₁ P₂ Q₁ Q₂ : Type*} [Field K] [AddCommGroup W] [Module K W]
  [AddCommGroup P₁] [Module K P₁] [AddCommGroup P₂] [Module K P₂]
  [AddCommGroup Q₁] [Module K Q₁] [AddCommGroup Q₂] [Module K Q₂]
  {ω : LinearMap.BilinForm K W}

theorem FourPieces.a₂_eq_zero_left (hω : ω.Nondegenerate) (F : FourPieces ω P₁ P₂ Q₁ Q₂) {p : P₂}
    (h : ∀ q, F.a₂ p q = 0) : p = 0 := by
  have hw : F.incP₂ p = 0 := hω.1 _ fun w' ↦ by
    rw [F.form, FourPieces.incP₂_apply, LinearEquiv.apply_symm_apply]
    simp [h]
  have h2 := congrArg (fun w ↦ (F.e w).1.2) hw
  simpa [FourPieces.incP₂_apply] using h2

theorem FourPieces.a₂_eq_zero_right (hω : ω.Nondegenerate) (F : FourPieces ω P₁ P₂ Q₁ Q₂) {q : Q₂}
    (h : ∀ p, F.a₂ p q = 0) : q = 0 := by
  have hw : F.incQ₂ q = 0 := hω.2 _ fun w' ↦ by
    rw [F.form, FourPieces.incQ₂_apply, LinearEquiv.apply_symm_apply]
    simp [h]
  have h2 := congrArg (fun w ↦ (F.e w).2.2) hw
  simpa [FourPieces.incQ₂_apply] using h2

variable [FiniteDimensional K P₂] [FiniteDimensional K Q₂]

theorem FourPieces.finrank_P₂_eq_finrank_Q₂ (hω : ω.Nondegenerate) (F : FourPieces ω P₁ P₂ Q₁ Q₂) :
    finrank K P₂ = finrank K Q₂ := by
  have h1 : Function.Injective F.a₂ := (injective_iff_map_eq_zero _).mpr fun p hp ↦
    FourPieces.a₂_eq_zero_left hω F fun q ↦ by rw [hp]; rfl
  have h2 : Function.Injective F.a₂.flip := (injective_iff_map_eq_zero _).mpr fun q hq ↦
    FourPieces.a₂_eq_zero_right hω F fun p ↦ by
      have := LinearMap.congr_fun hq p
      simpa using this
  have i1 := LinearMap.finrank_le_finrank_of_injective h1
  have i2 := LinearMap.finrank_le_finrank_of_injective h2
  rw [Subspace.dual_finrank_eq] at i1 i2
  omega

def FourPieces.a₂DualEquiv (hω : ω.Nondegenerate) (F : FourPieces ω P₁ P₂ Q₁ Q₂) {ξ : K} (hξ : ξ ≠ 0) :
    Q₂ ≃ₗ[K] Module.Dual K P₂ :=
  LinearMap.linearEquivOfInjective (ξ • F.a₂.flip)
    ((injective_iff_map_eq_zero _).mpr fun q hq ↦ FourPieces.a₂_eq_zero_right hω F fun p ↦ by
      have := LinearMap.congr_fun hq p
      simp only [LinearMap.smul_apply, LinearMap.flip_apply, smul_eq_mul, LinearMap.zero_apply,
        mul_eq_zero, hξ, false_or] at this
      exact this)
    (by rw [Subspace.dual_finrank_eq, FourPieces.finrank_P₂_eq_finrank_Q₂ hω F])

theorem FourPieces.a₂DualEquiv_apply (hω : ω.Nondegenerate) (F : FourPieces ω P₁ P₂ Q₁ Q₂) {ξ : K}
    (hξ : ξ ≠ 0) (q : Q₂) (p : P₂) : FourPieces.a₂DualEquiv hω F hξ q p = ξ * F.a₂ p q := rfl

def FourPieces.a₂PairedBasis (hω : ω.Nondegenerate) (F : FourPieces ω P₁ P₂ Q₁ Q₂) {ξ : K}
    (hξ : ξ ≠ 0) : Basis (Fin (finrank K P₂)) K Q₂ :=
  (Module.finBasis K P₂).dualBasis.map (FourPieces.a₂DualEquiv hω F hξ).symm

theorem FourPieces.a₂_a₂PairedBasis (hω : ω.Nondegenerate) (F : FourPieces ω P₁ P₂ Q₁ Q₂) {ξ : K}
    (hξ : ξ ≠ 0) (i j : Fin (finrank K P₂)) :
    F.a₂ (Module.finBasis K P₂ i) (FourPieces.a₂PairedBasis hω F hξ j) = ξ⁻¹ * (if i = j then 1 else 0) := by
  have h : FourPieces.a₂DualEquiv hω F hξ (FourPieces.a₂PairedBasis hω F hξ j) = (Module.finBasis K P₂).dualBasis j := by
    rw [FourPieces.a₂PairedBasis, Basis.map_apply, LinearEquiv.apply_symm_apply]
  have h2 := LinearMap.congr_fun h (Module.finBasis K P₂ i)
  rw [FourPieces.a₂DualEquiv_apply, Basis.dualBasis_apply_self] at h2
  rw [← h2, ← mul_assoc, inv_mul_cancel₀ hξ, one_mul]

end Pairing

section Adelic

variable {K W P₁ P₂ Q₁ Q₂ : Type*} [Field K] [NumberField K] [AddCommGroup W] [Module K W]
  [AddCommGroup P₁] [Module K P₁] [AddCommGroup P₂] [Module K P₂]
  [AddCommGroup Q₁] [Module K Q₁] [AddCommGroup Q₂] [Module K Q₂]
  {ω : LinearMap.BilinForm K W}

theorem FourPieces.adelicPairing₂_adelicCoord_symm [FiniteDimensional K P₂] [FiniteDimensional K Q₂]
    (hω : ω.Nondegenerate) (F : FourPieces ω P₁ P₂ Q₁ Q₂) {ξ : K} (hξ : ξ ≠ 0)
    (x y : Fin (finrank K P₂) → 𝔸[K]) :
    F.adelicPairing₂ ((adelicCoord (Module.finBasis K P₂)).symm x)
        ((adelicCoord (FourPieces.a₂PairedBasis hω F hξ)).symm y) =
      algebraMap K 𝔸[K] ξ⁻¹ * ∑ i, x i * y i := by
  have hij : ∀ i j, ω.baseChange 𝔸[K] (F.incP₂.baseChange 𝔸[K] ((1 : 𝔸[K]) ⊗ₜ Module.finBasis K P₂ i))
      (F.incQ₂.baseChange 𝔸[K] ((1 : 𝔸[K]) ⊗ₜ FourPieces.a₂PairedBasis hω F hξ j)) =
      algebraMap K 𝔸[K] ξ⁻¹ * (if i = j then 1 else 0) := by
    intro i j
    have h := F.adelicPairing₂_tmul 1 1 (Module.finBasis K P₂ i) (FourPieces.a₂PairedBasis hω F hξ j)
    rw [FourPieces.adelicPairing₂] at h
    rw [h, FourPieces.a₂_a₂PairedBasis, mul_one, map_mul]
    split_ifs <;> simp
  rw [adelicCoord_symm_apply, adelicCoord_symm_apply]
  simp only [FourPieces.adelicPairing₂, map_sum, map_smul, LinearMap.sum_apply,
    LinearMap.smul_apply, smul_eq_mul, hij, mul_ite, mul_zero, mul_one,
    Finset.mem_univ, if_true, Finset.sum_ite_eq']
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ ↦ by ring

theorem adelicCoord_prod_symm_sumElim [FiniteDimensional K P₁] [FiniteDimensional K P₂] {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] (b₁ : Basis ι K P₁) (b₂ : Basis κ K P₂) (a : ι → 𝔸[K]) (x : κ → 𝔸[K]) :
    (adelicCoord (b₁.prod b₂)).symm (Sum.elim a x) =
      (adelicProdEquiv K P₁ P₂).symm ((adelicCoord b₁).symm a, (adelicCoord b₂).symm x) := by
  apply (adelicProdEquiv K P₁ P₂).injective
  rw [LinearEquiv.apply_symm_apply, adelicCoord_symm_apply, adelicCoord_symm_apply,
    adelicCoord_symm_apply, map_sum, Fintype.sum_sum_type]
  ext <;> simp [Basis.prod_apply, Prod.fst_sum, Prod.snd_sum]

theorem schwartzBruhatPoints_prodSlice_mem [FiniteDimensional K P₁] [FiniteDimensional K P₂]
    {φ : AdelicPoints K (P₁ × P₂) → ℂ} (hφ : φ ∈ schwartzBruhatPoints K (P₁ × P₂))
    (p₁ : AdelicPoints K P₁) :
    (fun p ↦ φ ((adelicProdEquiv K P₁ P₂).symm (p₁, p))) ∈ schwartzBruhatPoints K P₂ := by
  rw [mem_schwartzBruhatPoints_iff ((Module.finBasis K P₁).prod (Module.finBasis K P₂))] at hφ
  rw [mem_schwartzBruhatPoints_iff (Module.finBasis K P₂)]
  have h := schwartzBruhatPi_sumElim_mem hφ (adelicCoord (Module.finBasis K P₁) p₁)
  convert h using 1
  funext x
  simp only [Function.comp_apply, adelicCoord_prod_symm_sumElim, LinearEquiv.symm_apply_apply]

theorem FourPieces.adelicFourierInversion_P₂ [FiniteDimensional K P₂] [FiniteDimensional K Q₂]
    (hω : ω.Nondegenerate) (F : FourPieces ω P₁ P₂ Q₁ Q₂) {ψ : AddChar 𝔸[K] Circle} {ξ : K}
    (hξ : ξ ≠ 0) (hψ : ∀ x, ψ x = adelicChar K (algebraMap K 𝔸[K] ξ * x))
    {f : AdelicPoints K P₂ → ℂ} (hf : f ∈ schwartzBruhatPoints K P₂) (p₂ : AdelicPoints K P₂) :
    ∫ q, (∫ p, f p * (ψ (F.adelicPairing₂ p q) : ℂ) ∂adelicPointsMeasure K P₂) *
        (ψ (-F.adelicPairing₂ p₂ q) : ℂ) ∂adelicPointsMeasure K Q₂ = f p₂ := by
  set b := Module.finBasis K P₂
  set c := FourPieces.a₂PairedBasis hω F hξ
  set G := f ∘ (adelicCoord b).symm with hGdef
  have hG : G ∈ schwartzBruhatPi K (Fin (finrank K P₂)) := (mem_schwartzBruhatPoints_iff b).mp hf
  obtain ⟨x₀, rfl⟩ : ∃ x₀, (adelicCoord b).symm x₀ = p₂ :=
    ⟨adelicCoord b p₂, LinearEquiv.symm_apply_apply _ _⟩
  have hchar : ∀ x y, (ψ (F.adelicPairing₂ ((adelicCoord b).symm x) ((adelicCoord c).symm y)) : ℂ) =
      adelicChar K (∑ i, x i * y i) := by
    intro x y
    rw [hψ, FourPieces.adelicPairing₂_adelicCoord_symm, ← mul_assoc, ← map_mul, mul_inv_cancel₀ hξ, map_one, one_mul]
  have hchar' : ∀ y, (ψ (-F.adelicPairing₂ ((adelicCoord b).symm x₀) ((adelicCoord c).symm y)) : ℂ) =
      adelicChar K (∑ i, y i * (-x₀) i) := by
    intro y
    rw [hψ, FourPieces.adelicPairing₂_adelicCoord_symm, mul_neg, ← mul_assoc, ← map_mul, mul_inv_cancel₀ hξ, map_one,
      one_mul, ← Finset.sum_neg_distrib]
    congr 2
    exact Finset.sum_congr rfl fun i _ ↦ by rw [Pi.neg_apply]; ring
  have hinner : ∀ y, ∫ p, f p * (ψ (F.adelicPairing₂ p ((adelicCoord c).symm y)) : ℂ)
      ∂adelicPointsMeasure K P₂ = adelicFourierPi K G y := by
    intro y
    rw [adelicPointsMeasure_eq_map b, (measurableEmbedding_adelicCoord_symm b).integral_map]
    simp only [hchar]
    rfl
  rw [adelicPointsMeasure_eq_map c, (measurableEmbedding_adelicCoord_symm c).integral_map]
  simp only [hinner, hchar']
  have h := congrFun (adelicFourierPi_adelicFourierPi hG) (-x₀)
  simp only [neg_neg] at h
  exact h

end Adelic

end

end GroundTheory.Heights₂.Theta
