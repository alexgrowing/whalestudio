import Mathlib
import GroundTheory.HeightsAndTheta.Theta.EisensteinZeta.MirabolicInduction.CfunOmStatements
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Theta

open UpperHalfPlane ModularGroup Complex NumberField
open scoped Real MatrixGroups nonZeroDivisors

theorem image_mul_span_pair (u a b : ℂ) :
    (fun z => u * z) '' (Submodule.span ℤ ({a, b} : Set ℂ) : Set ℂ) =
      (Submodule.span ℤ ({u * a, u * b} : Set ℂ) : Set ℂ) := by
  have h := Submodule.map_span (LinearMap.mulLeft ℤ u) ({a, b} : Set ℂ)
  rw [Set.image_pair] at h
  simp only [LinearMap.mulLeft_apply] at h
  rw [← h, Submodule.map_coe]
  rfl

theorem image_mul_latticeOf (u τ : ℂ) :
    (fun z => u * z) '' latticeOf τ = (Submodule.span ℤ ({u, u * τ} : Set ℂ) : Set ℂ) := by
  rw [latticeOf, image_mul_span_pair, mul_one]

theorem latticeOf_neg (t : ℂ) : latticeOf (-t) = latticeOf t := by
  unfold latticeOf
  congr 1
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro x (rfl | rfl)
    · exact Submodule.subset_span (by simp)
    · exact Submodule.neg_mem _ (Submodule.subset_span (by simp))
  · rw [Submodule.span_le]
    rintro x (rfl | rfl)
    · exact Submodule.subset_span (by simp)
    · have : -(-x) ∈ Submodule.span ℤ ({1, -x} : Set ℂ) :=
        Submodule.neg_mem _ (Submodule.subset_span (by simp))
      simpa using this

theorem span_denom_num_eq (g : SL(2, ℤ)) (τ : ℂ) :
    Submodule.span ℤ ({(g 1 0 : ℂ) * τ + g 1 1, (g 0 0 : ℂ) * τ + g 0 1} : Set ℂ) =
      Submodule.span ℤ ({1, τ} : Set ℂ) := by
  have hdet : (g 0 0 : ℂ) * g 1 1 - g 0 1 * g 1 0 = 1 := by
    have := g.det_coe
    rw [Matrix.det_fin_two] at this
    exact_mod_cast this
  apply le_antisymm
  · rw [Submodule.span_le, Set.insert_subset_iff, Set.singleton_subset_iff]
    refine ⟨?_, ?_⟩
    · exact Submodule.mem_span_pair.mpr ⟨g 1 1, g 1 0, by simp [zsmul_eq_mul]; ring⟩
    · exact Submodule.mem_span_pair.mpr ⟨g 0 1, g 0 0, by simp [zsmul_eq_mul]; ring⟩
  · rw [Submodule.span_le, Set.insert_subset_iff, Set.singleton_subset_iff]
    refine ⟨?_, ?_⟩
    · refine Submodule.mem_span_pair.mpr ⟨g 0 0, -g 1 0, ?_⟩
      simp only [zsmul_eq_mul, Int.cast_neg]
      linear_combination hdet
    · refine Submodule.mem_span_pair.mpr ⟨-g 0 1, g 1 1, ?_⟩
      simp only [zsmul_eq_mul, Int.cast_neg]
      linear_combination τ * hdet

theorem IsLatticeParam.smul {Λ : Set ℂ} {τ : ℍ} (h : IsLatticeParam Λ τ) (g : SL(2, ℤ)) :
    IsLatticeParam Λ (g • τ) := by
  obtain ⟨c, hc, hΛ⟩ := h
  set D : ℂ := (g 1 0 : ℂ) * τ + g 1 1 with hD
  have hD0 : D ≠ 0 := by
    have := UpperHalfPlane.denom_ne_zero (g : GL (Fin 2) ℝ) τ
    simpa [UpperHalfPlane.denom, D] using this
  have hgτ : ((g • τ : ℍ) : ℂ) = ((g 0 0 : ℂ) * τ + g 0 1) / D := by
    rw [UpperHalfPlane.coe_specialLinearGroup_apply]
    simp [D]
  have key : (fun z => D * z) '' latticeOf ((g • τ : ℍ) : ℂ) = latticeOf (τ : ℂ) := by
    rw [image_mul_latticeOf, hgτ, mul_div_cancel₀ _ hD0, latticeOf, span_denom_num_eq]
  refine ⟨D⁻¹ * c, mul_ne_zero (inv_ne_zero hD0) hc, ?_⟩
  have : (fun z => D⁻¹ * c * z) '' Λ = (fun z => D⁻¹ * z) '' ((fun z => c * z) '' Λ) := by
    rw [Set.image_image]; simp [mul_assoc]
  rw [this, hΛ, ← key, Set.image_image]
  simp [inv_mul_cancel_left₀ hD0]

variable {K : Type*} [Field K] [NumberField K]

theorem im_div_ne_zero_of_basis (σ : K →+* ℂ) (hσ : ∃ x : K, (σ x).im ≠ 0)
    {ι : Type*} (b : Module.Basis ι ℚ K) (e : ι ≃ Fin 2) :
    (σ (b (e.symm 1)) / σ (b (e.symm 0))).im ≠ 0 := by
  set w : ℂ := (σ (b (e.symm 0)))⁻¹ with hw
  intro h0
  have hall : ∀ x : K, (σ x * w).im = 0 := by
    intro x
    have hx : x ∈ Submodule.span ℚ (Set.range b) := by rw [b.span_eq]; trivial
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨i, rfl⟩ := hy
      obtain ⟨j, rfl⟩ := e.symm.surjective i
      fin_cases j
      · simp only [Fin.zero_eta, w]
        rw [mul_inv_cancel₀]
        · simp
        · exact (map_ne_zero σ).mpr (b.ne_zero _)
      · simpa [div_eq_mul_inv, w] using h0
    | zero => simp
    | add y z _ _ hy hz => simp [add_mul, hy, hz]
    | smul q y _ hy =>
      rw [Rat.smul_def, map_mul, map_ratCast, mul_assoc]
      simp [hy]
  have hw0 : w ≠ 0 := inv_ne_zero ((map_ne_zero σ).mpr (b.ne_zero _))
  have hwim : w.im = 0 := by simpa using hall 1
  obtain ⟨x, hx⟩ := hσ
  apply hx
  have hxr : σ x = (σ x * w) * w⁻¹ := by field_simp
  have hwinv : (w⁻¹).im = 0 := by simp [Complex.inv_im, hwim]
  rw [hxr, Complex.mul_im, hall x, hwinv]
  ring

theorem exists_isLatticeParam_fractionalIdeal (h2 : Module.finrank ℚ K = 2) (σ : K →+* ℂ)
    (hσ : ∃ x : K, (σ x).im ≠ 0) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    ∃ τ : ℍ, IsLatticeParam (σ '' ((I : FractionalIdeal (𝓞 K)⁰ K) : Set K)) τ := by
  set b := basisOfFractionalIdeal K I
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex ℤ I) = 2 := by
    rw [← h2, Module.finrank_eq_card_basis b]
  let e : Module.Free.ChooseBasisIndex ℤ I ≃ Fin 2 := Fintype.equivFinOfCardEq hcard
  set ω₀ := b (e.symm 0)
  set ω₁ := b (e.symm 1)
  have hrange : Set.range b = {ω₀, ω₁} := by
    ext x
    simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨i, rfl⟩
      obtain ⟨j, rfl⟩ := e.symm.surjective i
      fin_cases j
      · left; rfl
      · right; rfl
    · rintro (rfl | rfl)
      · exact ⟨_, rfl⟩
      · exact ⟨_, rfl⟩
  have hI : ((I : FractionalIdeal (𝓞 K)⁰ K) : Set K) =
      (Submodule.span ℤ ({ω₀, ω₁} : Set K) : Set K) := by
    rw [← hrange]
    ext x
    exact (mem_span_basisOfFractionalIdeal (K := K) (I := I)).symm
  have hσI : σ '' ((I : FractionalIdeal (𝓞 K)⁰ K) : Set K) =
      (Submodule.span ℤ ({σ ω₀, σ ω₁} : Set ℂ) : Set ℂ) := by
    rw [hI]
    have h := Submodule.map_span σ.toAddMonoidHom.toIntLinearMap ({ω₀, ω₁} : Set K)
    rw [Set.image_pair] at h
    have h' := congrArg (fun p : Submodule ℤ ℂ => (p : Set ℂ)) h
    simpa [Submodule.map_coe] using h'
  have h0 : σ ω₀ ≠ 0 := (map_ne_zero σ).mpr (b.ne_zero _)
  set t : ℂ := σ ω₁ / σ ω₀
  have ht : t.im ≠ 0 := im_div_ne_zero_of_basis σ hσ b e
  have himage : (fun z => (σ ω₀)⁻¹ * z) '' (σ '' ((I : FractionalIdeal (𝓞 K)⁰ K) : Set K)) =
      latticeOf t := by
    rw [hσI, image_mul_span_pair, inv_mul_cancel₀ h0, latticeOf, inv_mul_eq_div]
  rcases lt_or_gt_of_ne ht with hneg | hpos
  · refine ⟨⟨-t, by simpa using hneg⟩, (σ ω₀)⁻¹, inv_ne_zero h0, ?_⟩
    show _ = latticeOf (-t)
    rw [latticeOf_neg, himage]
  · exact ⟨⟨t, hpos⟩, (σ ω₀)⁻¹, inv_ne_zero h0, himage⟩

theorem ClassReducedParamsNonempty.proof : ClassReducedParamsNonempty.Statement := by
  intro K _ _ h2 σ hσ A
  refine ClassGroup.induction (K := K) (fun I => ?_) A
  obtain ⟨τ, hτ⟩ := exists_isLatticeParam_fractionalIdeal h2 σ hσ I
  obtain ⟨g, hg⟩ := ModularGroup.exists_smul_mem_fd τ
  exact ⟨g • τ, I, rfl, hg, hτ.smul g⟩

end GroundTheory.Heights₂.Theta
