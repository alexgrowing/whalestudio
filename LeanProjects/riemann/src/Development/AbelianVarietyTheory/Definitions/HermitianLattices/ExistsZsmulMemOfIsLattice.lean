import Mathlib
import ReciprocityTheory.SemistableReduction.TorsionNonvanishStatement
import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.Imports

noncomputable section

namespace GlobalTheory

open NumberField Matrix
open ReciprocityTheory.MultiplicativeHeights (IsLattice)
open scoped TensorProduct nonZeroDivisors

variable {r : ℕ}

section Lattice

variable {K : Type} [Field K] [NumberField K]
variable {M M' : Type} [AddCommGroup M] [Module (𝓞 K) M] [AddCommGroup M'] [Module (𝓞 K) M']

theorem exists_zsmul_mem_of_isLattice {Λ : Submodule (𝓞 K) (Fin r → K)} (hΛ : IsLattice Λ)
    (v : Fin r → K) : ∃ n : ℤ, n ≠ 0 ∧ n • v ∈ Λ := by
  first
  | exact @_root_.GlobalTheory.IntSmulIntegral.exists_int_smul_mem
  | exact _root_.GlobalTheory.IntSmulIntegral.exists_int_smul_mem
  | (apply _root_.GlobalTheory.IntSmulIntegral.exists_int_smul_mem <;> assumption)
  | (intros; apply _root_.GlobalTheory.IntSmulIntegral.exists_int_smul_mem <;> assumption)
  | (intros; apply @_root_.GlobalTheory.IntSmulIntegral.exists_int_smul_mem <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.IntSmulIntegral.exists_int_smul_mem ..)

def IsLatticeEmb (φ : M →ₗ[𝓞 K] (Fin r → K)) : Prop :=
  Function.Injective φ ∧ IsLattice (LinearMap.range φ)

theorem isLatticeEmb_subtype {Λ : Submodule (𝓞 K) (Fin r → K)} (hΛ : IsLattice Λ) :
    IsLatticeEmb Λ.subtype :=
  ⟨Λ.injective_subtype, by rwa [Submodule.range_subtype]⟩

theorem isLatticeEmb_of_span [Module.Finite (𝓞 K) M] {φ : M →ₗ[𝓞 K] (Fin r → K)}
    (hi : Function.Injective φ) (hs : Submodule.span K (Set.range φ) = ⊤) : IsLatticeEmb φ :=
  ⟨hi, by rw [LinearMap.range_eq_map]; exact Module.Finite.fg_top.map _, hs⟩

namespace IsLatticeEmb

variable {φ : M →ₗ[𝓞 K] (Fin r → K)}

theorem exists_zsmul (h : IsLatticeEmb φ) (v : Fin r → K) :
    ∃ n : ℤ, n ≠ 0 ∧ ∃ x, φ x = n • v :=
  exists_zsmul_mem_of_isLattice h.2 v

theorem finite (h : IsLatticeEmb φ) : Module.Finite (𝓞 K) M := by
  have : Module.Finite (𝓞 K) (LinearMap.range φ) := Module.Finite.iff_fg.mpr h.2.1
  exact Module.Finite.equiv (LinearEquiv.ofInjective φ h.1).symm

theorem isLocalizedModule_int (h : IsLatticeEmb φ) :
    IsLocalizedModule ℤ⁰ (φ.restrictScalars ℤ) where
  map_units s := by
    have hs : ((s : ℤ) : ℚ) ≠ 0 := by exact_mod_cast nonZeroDivisors.coe_ne_zero s
    rw [Module.End.isUnit_iff]
    have : ⇑(algebraMap ℤ (Module.End ℤ (Fin r → K)) s) = fun v => ((s : ℤ) : ℚ) • v := by
      funext v; rw [Module.algebraMap_end_apply, Int.cast_smul_eq_zsmul]
    rw [this]
    exact MulAction.bijective (Units.mk0 _ hs)
  surj v := by
    obtain ⟨n, hn, x, hx⟩ := h.exists_zsmul v
    exact ⟨(x, ⟨n, mem_nonZeroDivisors_of_ne_zero hn⟩), hx.symm⟩
  exists_of_eq hxy := ⟨1, by rw [h.1 hxy]⟩

theorem isLocalizedModule (h : IsLatticeEmb φ) : IsLocalizedModule (𝓞 K)⁰ φ where
  map_units s := by
    have hs : ((s : 𝓞 K) : K) ≠ 0 := by exact_mod_cast nonZeroDivisors.coe_ne_zero s
    rw [Module.End.isUnit_iff]
    have : ⇑(algebraMap (𝓞 K) (Module.End (𝓞 K) (Fin r → K)) s) = fun v => ((s : 𝓞 K) : K) • v := by
      funext v; rw [Module.algebraMap_end_apply, ← algebraMap_smul K]
    rw [this]
    exact MulAction.bijective (Units.mk0 _ hs)
  surj v := by
    obtain ⟨n, hn, x, hx⟩ := h.exists_zsmul v
    refine ⟨(x, ⟨(n : 𝓞 K), mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast hn)⟩), ?_⟩
    rw [hx, Submonoid.smul_def, Int.cast_smul_eq_zsmul]
  exists_of_eq hxy := ⟨1, by rw [h.1 hxy]⟩

theorem isBaseChange_rat (h : IsLatticeEmb φ) : IsBaseChange ℚ (φ.restrictScalars ℤ) :=
  (isLocalizedModule_iff_isBaseChange ℤ⁰ ℚ _).mp h.isLocalizedModule_int

theorem isBaseChange (h : IsLatticeEmb φ) : IsBaseChange K φ :=
  (isLocalizedModule_iff_isBaseChange (𝓞 K)⁰ K _).mp h.isLocalizedModule

theorem finrank_eq (h : IsLatticeEmb φ) : Module.finrank (𝓞 K) M = r := by
  rw [← h.isBaseChange.finrank_eq, Module.finrank_fin_fun]

theorem finrank_int_eq (h : IsLatticeEmb φ) : Module.finrank ℤ M = r * Module.finrank ℚ K := by
  rw [← h.isBaseChange_rat.finrank_eq, Module.finrank_pi_fintype]
  simp

theorem bilin_ext (h : IsLatticeEmb φ) {B B' : LinearMap.BilinForm ℚ (Fin r → K)}
    (hB : ∀ x y, B (φ x) (φ y) = B' (φ x) (φ y)) : B = B' := by
  refine LinearMap.ext₂ fun v w => ?_
  obtain ⟨m, hm, x, hx⟩ := h.exists_zsmul v
  obtain ⟨n, hn, y, hy⟩ := h.exists_zsmul w
  have := hB x y
  simp only [hx, hy, map_zsmul, LinearMap.smul_apply] at this
  exact smul_right_injective ℚ hm (smul_right_injective ℚ hn this)

theorem matrix_ext {s : ℕ} (h : IsLatticeEmb φ) {A A' : Matrix (Fin s) (Fin r) K}
    (hA : ∀ x, A *ᵥ φ x = A' *ᵥ φ x) : A = A' := by
  refine Matrix.ext_of_mulVec_single fun i => ?_
  obtain ⟨n, hn, x, hx⟩ := h.exists_zsmul (Pi.single i 1)
  have := hA x
  rw [hx, mulVec_smul, mulVec_smul] at this
  exact smul_right_injective _ hn this

theorem exists_matrix {s : ℕ} (h : IsLatticeEmb φ) (g : M →ₗ[𝓞 K] (Fin s → K)) :
    ∃ A : Matrix (Fin s) (Fin r) K, ∀ x, A *ᵥ φ x = g x :=
  ⟨LinearMap.toMatrix' (h.isBaseChange.lift g), fun x => by
    rw [← Matrix.toLin'_apply, Matrix.toLin'_toMatrix', IsBaseChange.lift_eq]⟩

theorem existsUnique_GL {φ' : M' →ₗ[𝓞 K] (Fin r → K)} (h : IsLatticeEmb φ) (h' : IsLatticeEmb φ')
    (g : M ≃ₗ[𝓞 K] M') :
    ∃! γ : GL (Fin r) K, ∀ x, (γ : Matrix (Fin r) (Fin r) K) *ᵥ φ x = φ' (g x) := by
  obtain ⟨A, hA⟩ := h.exists_matrix (φ' ∘ₗ g.toLinearMap)
  obtain ⟨A', hA'⟩ := h'.exists_matrix (φ ∘ₗ g.symm.toLinearMap)
  refine ⟨⟨A, A', h'.matrix_ext fun x => ?_, h.matrix_ext fun x => ?_⟩, hA, fun γ hγ => ?_⟩
  · rw [← mulVec_mulVec, hA', one_mulVec]; simp [hA]
  · rw [← mulVec_mulVec, hA, one_mulVec]; simp [hA']
  · exact Units.ext (h.matrix_ext fun x => by rw [hγ]; exact (hA x).symm)

theorem comp_GL (h : IsLatticeEmb φ) (γ : GL (Fin r) K) :
    IsLatticeEmb (((γ : Matrix (Fin r) (Fin r) K).mulVecLin.restrictScalars (𝓞 K)) ∘ₗ φ) := by
  have hγ : Function.Bijective (γ : Matrix (Fin r) (Fin r) K).mulVecLin :=
    ⟨mulVec_injective_iff_isUnit.mpr γ.isUnit, mulVec_surjective_iff_isUnit.mpr γ.isUnit⟩
  refine ⟨hγ.1.comp h.1, ?_, ?_⟩
  · rw [LinearMap.range_comp]; exact h.2.1.map _
  · rw [LinearMap.range_comp, Submodule.map_coe, LinearMap.coe_restrictScalars,
      ← Submodule.map_span, h.2.2, Submodule.map_top, LinearMap.range_eq_top.mpr hγ.2]

def extend (h : IsLatticeEmb φ) (β : LinearMap.BilinForm ℤ M) :
    LinearMap.BilinForm ℚ (Fin r → K) :=
  LinearMap.BilinForm.congr h.isBaseChange_rat.equiv (β.baseChange ℚ)

@[simp] theorem extend_apply (h : IsLatticeEmb φ) (β : LinearMap.BilinForm ℤ M) (x y : M) :
    h.extend β (φ x) (φ y) = β x y := by
  have e : ∀ z, h.isBaseChange_rat.equiv.symm (φ z) = 1 ⊗ₜ z := fun z =>
    h.isBaseChange_rat.equiv_symm_apply z
  rw [extend, LinearMap.BilinForm.congr_apply, e, e, LinearMap.BilinForm.baseChange_tmul]
  simp

theorem extend_isAlt (h : IsLatticeEmb φ) {β : LinearMap.BilinForm ℤ M} (hβ : ∀ x, β x x = 0) :
    (h.extend β).IsAlt := by
  intro v
  obtain ⟨n, hn, x, hx⟩ := h.exists_zsmul v
  have := h.extend_apply β x x
  simp only [hx, hβ, map_zsmul, LinearMap.smul_apply, Int.cast_zero, smul_eq_zero, hn,
    false_or] at this
  exact this

theorem extend_nondegenerate_iff (h : IsLatticeEmb φ) (β : LinearMap.BilinForm ℤ M) :
    (h.extend β).Nondegenerate ↔ Function.Injective β := by
  rw [injective_iff_map_eq_zero]
  constructor
  · intro hn x hx
    apply h.1
    rw [map_zero]
    refine hn.1 _ fun w => ?_
    obtain ⟨n, hn0, y, hy⟩ := h.exists_zsmul w
    have := h.extend_apply β x y
    rw [hy, hx, map_zsmul, LinearMap.zero_apply, Int.cast_zero] at this
    exact (smul_eq_zero.mp this).resolve_left hn0
  · intro hβ
    refine LinearMap.BilinForm.Nondegenerate.ofSeparatingLeft fun v hv => ?_
    obtain ⟨n, hn, x, hx⟩ := h.exists_zsmul v
    have : x = 0 := hβ x (LinearMap.ext fun y => by
      have := h.extend_apply β x y
      rw [hx, map_zsmul, LinearMap.smul_apply, hv, smul_zero] at this
      exact_mod_cast this.symm)
    rw [this, map_zero] at hx
    exact (smul_eq_zero.mp hx.symm).resolve_left hn

end IsLatticeEmb

theorem exists_isLatticeEmb [Module.Finite (𝓞 K) M] [Module.IsTorsionFree (𝓞 K) M]
    (hr : Module.finrank (𝓞 K) M = r) : ∃ φ : M →ₗ[𝓞 K] (Fin r → K), IsLatticeEmb φ := by
  have hb := TensorProduct.isBaseChange (𝓞 K) M K
  have hfin : Module.finrank K (K ⊗[𝓞 K] M) = r := by rw [hb.finrank_eq, hr]
  let e : (K ⊗[𝓞 K] M) ≃ₗ[K] (Fin r → K) := (Module.finBasisOfFinrankEq K _ hfin).equivFun
  have hloc : IsLocalizedModule (𝓞 K)⁰ (TensorProduct.mk (𝓞 K) K M 1) :=
    (isLocalizedModule_iff_isBaseChange (𝓞 K)⁰ K _).mpr hb
  refine ⟨(e.toLinearMap.restrictScalars (𝓞 K)) ∘ₗ TensorProduct.mk (𝓞 K) K M 1, ?_, ?_, ?_⟩
  · refine e.injective.comp ((injective_iff_map_eq_zero _).mpr fun x hx => ?_)
    obtain ⟨s, hs⟩ := (IsLocalizedModule.eq_zero_iff (𝓞 K)⁰ _).mp hx
    exact (smul_eq_zero.mp hs).resolve_left (nonZeroDivisors.coe_ne_zero s)
  · rw [LinearMap.range_eq_map]; exact Module.Finite.fg_top.map _
  · rw [LinearMap.range_comp, Submodule.map_coe, LinearMap.coe_restrictScalars,
      ← Submodule.map_span]
    have : Submodule.span K (LinearMap.range (TensorProduct.mk (𝓞 K) K M 1) : Set (K ⊗[𝓞 K] M)) = ⊤ := by
      rw [eq_top_iff]
      rintro z -
      induction z using TensorProduct.induction_on with
      | zero => exact zero_mem _
      | tmul a x =>
        have : a ⊗ₜ[𝓞 K] x = a • (TensorProduct.mk (𝓞 K) K M 1 x) := by
          simp [TensorProduct.smul_tmul']
        rw [this]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨x, rfl⟩)
      | add u v hu hv => exact add_mem hu hv
    rw [this, Submodule.map_top, LinearEquiv.range]

end Lattice

example {K : Type} [Field K] [NumberField K] :
    IsLatticeEmb ((Algebra.linearMap (𝓞 K) K).compLeft (Fin r)) := by
  refine isLatticeEmb_of_span (fun x y h => funext fun i => RingOfIntegers.ext (congrFun h i)) ?_
  rw [eq_top_iff, ← (Pi.basisFun K (Fin r)).span_eq]
  refine Submodule.span_mono ?_
  rintro _ ⟨i, rfl⟩
  refine ⟨Pi.single i 1, funext fun j => ?_⟩
  by_cases h : j = i
  · subst h; simp
  · simp [h]

end GlobalTheory
