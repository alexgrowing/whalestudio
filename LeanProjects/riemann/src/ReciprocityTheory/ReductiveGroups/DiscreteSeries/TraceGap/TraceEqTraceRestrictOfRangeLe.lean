import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.LinearAlgebra.Trace

noncomputable section

namespace ReciprocityTheory.ChartRestriction.DS.TRGap

section LA

variable {Y : Type*} [AddCommGroup Y] [Module ℂ Y] [FiniteDimensional ℂ Y]

theorem trace_eq_trace_restrict_of_range_le (f : Y →ₗ[ℂ] Y) (Y0 : Submodule ℂ Y)
    (h : LinearMap.range f ≤ Y0) :
    LinearMap.trace ℂ Y f =
      LinearMap.trace ℂ Y0 (f.restrict (fun x _ => h (LinearMap.mem_range_self f x))) := by
  have hm : ∀ x, f x ∈ Y0 := fun x => h (LinearMap.mem_range_self f x)
  calc LinearMap.trace ℂ Y f = LinearMap.trace ℂ Y (Y0.subtype ∘ₗ LinearMap.codRestrict Y0 f hm) := by
        rw [LinearMap.subtype_comp_codRestrict]
    _ = LinearMap.trace ℂ Y0 (LinearMap.codRestrict Y0 f hm ∘ₗ Y0.subtype) :=
        LinearMap.trace_comp_comm' _ _
    _ = _ := by
        congr 1

theorem trace_eq_add_of_isCompl (f : Y →ₗ[ℂ] Y) {K R : Submodule ℂ Y} (hKR : IsCompl K R)
    (hK : ∀ x ∈ K, f x ∈ K) (hR : ∀ x ∈ R, f x ∈ R) :
    LinearMap.trace ℂ Y f = LinearMap.trace ℂ K (f.restrict hK) + LinearMap.trace ℂ R (f.restrict hR) := by
  have hrK : LinearMap.range (f ∘ₗ K.projection R hKR) ≤ K := by
    rintro _ ⟨x, rfl⟩
    exact hK _ (Submodule.projection_apply_mem _ _)
  have hrR : LinearMap.range (f ∘ₗ R.projection K hKR.symm) ≤ R := by
    rintro _ ⟨x, rfl⟩
    exact hR _ (Submodule.projection_apply_mem _ _)
  have h1 : LinearMap.trace ℂ Y f = LinearMap.trace ℂ Y (f ∘ₗ K.projection R hKR) +
      LinearMap.trace ℂ Y (f ∘ₗ R.projection K hKR.symm) := by
    rw [← map_add, ← LinearMap.comp_add, Submodule.projection_add_projection_eq_id, LinearMap.comp_id]
  rw [h1, trace_eq_trace_restrict_of_range_le _ K hrK, trace_eq_trace_restrict_of_range_le _ R hrR]
  congr 2
  · ext x
    simp
  · ext x
    simp

end LA

section S4

variable {Y : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [FiniteDimensional ℂ Y]

theorem str_eq_str_ker (Dl Γ B : Y →ₗ[ℂ] Y) (hD : ∀ x y, inner ℂ (Dl x) y = inner ℂ x (Dl y))
    (hΓD : ∀ x, Γ (Dl x) = -Dl (Γ x)) (hBD : ∀ x, B (Dl x) = Dl (B x)) :
    ∃ hk : ∀ x ∈ LinearMap.ker Dl, (Γ ∘ₗ B) x ∈ LinearMap.ker Dl,
      LinearMap.trace ℂ Y (Γ ∘ₗ B) = LinearMap.trace ℂ (LinearMap.ker Dl) ((Γ ∘ₗ B).restrict hk) := by
  have hDΓ : ∀ y, Dl (Γ y) = -Γ (Dl y) := fun y => by rw [hΓD, neg_neg]
  have hk : ∀ x ∈ LinearMap.ker Dl, (Γ ∘ₗ B) x ∈ LinearMap.ker Dl := by
    intro x hx
    rw [LinearMap.mem_ker] at hx ⊢
    rw [LinearMap.comp_apply, hDΓ, ← hBD, hx, map_zero, map_zero, neg_zero]
  refine ⟨hk, ?_⟩
  have hsym : Dl.IsSymmetric := hD
  have hkr : IsCompl (LinearMap.ker Dl) (LinearMap.range Dl) := by
    have := (Submodule.isCompl_orthogonal (LinearMap.range Dl)).symm
    rwa [hsym.orthogonal_range] at this
  have hV : ∀ x ∈ LinearMap.range Dl, (Γ ∘ₗ B) x ∈ LinearMap.range Dl := by
    rintro _ ⟨y, rfl⟩
    refine ⟨-Γ (B y), ?_⟩
    rw [map_neg, hDΓ, neg_neg, LinearMap.comp_apply, hBD]
  rw [trace_eq_add_of_isCompl _ hkr hk hV]
  suffices h0 : LinearMap.trace ℂ (LinearMap.range Dl) ((Γ ∘ₗ B).restrict hV) = 0 by
    rw [h0, add_zero]
  have hDV : ∀ x ∈ LinearMap.range Dl, Dl x ∈ LinearMap.range Dl := fun x _ => LinearMap.mem_range_self Dl x
  have hΓV : ∀ x ∈ LinearMap.range Dl, Γ x ∈ LinearMap.range Dl := by
    rintro _ ⟨y, rfl⟩
    exact ⟨-Γ y, by rw [map_neg, hDΓ, neg_neg]⟩
  have hBV : ∀ x ∈ LinearMap.range Dl, B x ∈ LinearMap.range Dl := by
    rintro _ ⟨y, rfl⟩
    exact ⟨B y, (hBD y).symm⟩
  have hinj : Function.Injective (Dl.restrict hDV) := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro v hv
    have hv' : (v : Y) ∈ LinearMap.ker Dl := by
      rw [LinearMap.mem_ker]
      have := congrArg Subtype.val (LinearMap.mem_ker.1 hv)
      simpa using this
    exact Subtype.ext (Submodule.disjoint_def.1 hkr.disjoint _ hv' v.2)
  set e := LinearEquiv.ofInjectiveEndo (Dl.restrict hDV) hinj
  have hsplit : (Γ ∘ₗ B).restrict hV = Γ.restrict hΓV ∘ₗ B.restrict hBV := by
    ext v
    rfl
  have hconj : e.conj ((Γ ∘ₗ B).restrict hV) = -((Γ ∘ₗ B).restrict hV) := by
    ext v
    obtain ⟨w, rfl⟩ : ∃ w, v = e w := ⟨e.symm v, (e.apply_symm_apply v).symm⟩
    simp only [LinearEquiv.conj_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply,
      LinearMap.neg_apply]
    show ((Dl.restrict hDV) ((Γ ∘ₗ B).restrict hV w) : Y) = -(((Γ ∘ₗ B).restrict hV (Dl.restrict hDV w)) : Y)
    simp only [LinearMap.restrict_apply, LinearMap.comp_apply]
    rw [hDΓ, ← hBD]
  have ht := LinearMap.trace_conj' ((Γ ∘ₗ B).restrict hV) e
  rw [hconj, map_neg] at ht
  linear_combination -ht / 2

end S4

end ReciprocityTheory.ChartRestriction.DS.TRGap
