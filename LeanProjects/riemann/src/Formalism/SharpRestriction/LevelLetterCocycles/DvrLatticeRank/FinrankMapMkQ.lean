import Mathlib

noncomputable section

namespace Formalism.MainNotions.N.Ln34.UniversalFiltration

open Module

variable {LL X : Type*} [Field LL] [AddCommGroup X] [Module LL X]

theorem finrank_map_mkQ (Oth S : Submodule LL X) (h : Disjoint S Oth) :
    finrank LL ↥(S.map Oth.mkQ) = finrank LL ↥S := by
  have hinj : Function.Injective (Oth.mkQ ∘ₗ S.subtype) := by
    intro x y hxy
    have hxy' : Oth.mkQ (x : X) = Oth.mkQ (y : X) := hxy
    simp only [Submodule.mkQ_apply] at hxy'
    rw [Submodule.Quotient.eq] at hxy'
    have h0 : (x : X) - y = 0 := (Submodule.disjoint_def.mp h) _ (sub_mem x.2 y.2) hxy'
    exact Subtype.ext (sub_eq_zero.mp h0)
  have hr : LinearMap.range (Oth.mkQ ∘ₗ S.subtype) = S.map Oth.mkQ := by
    rw [LinearMap.range_comp, Submodule.range_subtype]
  calc finrank LL ↥(S.map Oth.mkQ)
        = finrank LL ↥(LinearMap.range (Oth.mkQ ∘ₗ S.subtype)) := by rw [hr]
    _ = finrank LL ↥S := ((LinearEquiv.ofInjective _ hinj).finrank_eq).symm

theorem match_fil (I D Oth : Submodule LL X) [FiniteDimensional LL ↥I] [FiniteDimensional LL ↥D]
    (hDO : Disjoint D Oth) (hdim : finrank LL ↥I = finrank LL ↥D) (hDI : D ≤ I ⊔ Oth) :
    Disjoint I Oth ∧ ∀ F : Submodule LL X, F ≤ D → finrank LL ↥(I ⊓ (F ⊔ Oth)) = finrank LL ↥F := by
  have hsupmap : ∀ P : Submodule LL X, (P ⊔ Oth).map Oth.mkQ = P.map Oth.mkQ := by
    intro P
    first
      | rw [Submodule.map_sup, Submodule.mkQ_map_self, sup_bot_eq]
      | simp [Submodule.map_sup]
  have hmap : D.map Oth.mkQ ≤ I.map Oth.mkQ := by
    calc D.map Oth.mkQ ≤ (I ⊔ Oth).map Oth.mkQ := Submodule.map_mono hDI
      _ = I.map Oth.mkQ := hsupmap I
  haveI hfin : FiniteDimensional LL ↥(I.map Oth.mkQ) := by
    first
      | infer_instance
      | exact Module.Finite.map I Oth.mkQ
  have hDmap : finrank LL ↥(D.map Oth.mkQ) = finrank LL ↥D :=
    finrank_map_mkQ Oth D hDO
  have hIle : finrank LL ↥(I.map Oth.mkQ) ≤ finrank LL ↥I := by
    first
      | exact Submodule.finrank_map_le _ _
      | apply Submodule.finrank_map_le
  have hle2 : finrank LL ↥(D.map Oth.mkQ) ≤ finrank LL ↥(I.map Oth.mkQ) := by
    first
      | exact Submodule.finrank_le_finrank_of_le hmap
      | exact LinearMap.finrank_le_finrank_of_injective (Submodule.inclusion_injective hmap)
  have hIeq : finrank LL ↥(I.map Oth.mkQ) = finrank LL ↥I := by omega
  have hrI : LinearMap.range (Oth.mkQ ∘ₗ I.subtype) = I.map Oth.mkQ := by
    rw [LinearMap.range_comp, Submodule.range_subtype]
  have hrn := LinearMap.finrank_range_add_finrank_ker (Oth.mkQ ∘ₗ I.subtype)
  have hr' : finrank LL ↥(LinearMap.range (Oth.mkQ ∘ₗ I.subtype)) = finrank LL ↥I := by
    rw [hrI]; exact hIeq
  have hk : finrank LL ↥(LinearMap.ker (Oth.mkQ ∘ₗ I.subtype)) = 0 := by omega
  have hkb : LinearMap.ker (Oth.mkQ ∘ₗ I.subtype) = ⊥ := by
    first
      | exact Submodule.finrank_eq_zero.mp hk
      | exact (Submodule.finrank_eq_zero (S := LinearMap.ker (Oth.mkQ ∘ₗ I.subtype))).mp hk
      | (haveI := Module.finrank_zero_iff.mp hk; exact Submodule.eq_bot_of_subsingleton)
  have hinj : Function.Injective (Oth.mkQ ∘ₗ I.subtype) := LinearMap.ker_eq_bot.mp hkb
  have hdisj : Disjoint I Oth := by
    rw [Submodule.disjoint_def]
    intro x hxI hxO
    have h1 : (Oth.mkQ ∘ₗ I.subtype) ⟨x, hxI⟩ = (Oth.mkQ ∘ₗ I.subtype) 0 := by
      rw [map_zero]
      show Oth.mkQ x = 0
      first
        | (rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]; exact hxO)
        | simp [hxO]
    have h2 := hinj h1
    first
      | exact congrArg Subtype.val h2
      | simpa using congrArg Subtype.val h2
  refine ⟨hdisj, fun F hF => ?_⟩
  have hFO : Disjoint F Oth := hDO.mono_left hF
  have hJO : Disjoint (I ⊓ (F ⊔ Oth)) Oth := hdisj.mono_left inf_le_left
  have heq : (I ⊓ (F ⊔ Oth)).map Oth.mkQ = F.map Oth.mkQ := by
    apply le_antisymm
    · calc (I ⊓ (F ⊔ Oth)).map Oth.mkQ ≤ (F ⊔ Oth).map Oth.mkQ := Submodule.map_mono inf_le_right
        _ = F.map Oth.mkQ := hsupmap F
    · intro y hy
      obtain ⟨f, hfF, rfl⟩ := Submodule.mem_map.mp hy
      have hfD : Oth.mkQ f ∈ I.map Oth.mkQ := hmap (Submodule.mem_map.mpr ⟨f, hF hfF, rfl⟩)
      obtain ⟨i, hiI, hif⟩ := Submodule.mem_map.mp hfD
      have hsub : i - f ∈ Oth := by
        simp only [Submodule.mkQ_apply] at hif
        exact (Submodule.Quotient.eq Oth).mp hif
      have h3 : f + (i - f) ∈ F ⊔ Oth := Submodule.add_mem_sup hfF hsub
      have hi : i ∈ F ⊔ Oth := by
        first
          | simpa using h3
          | (rw [add_sub_cancel] at h3; exact h3)
      exact Submodule.mem_map.mpr ⟨i, Submodule.mem_inf.mpr ⟨hiI, hi⟩, hif⟩
  calc finrank LL ↥(I ⊓ (F ⊔ Oth))
        = finrank LL ↥((I ⊓ (F ⊔ Oth)).map Oth.mkQ) :=
          (finrank_map_mkQ Oth _ hJO).symm
    _ = finrank LL ↥(F.map Oth.mkQ) := by rw [heq]
    _ = finrank LL ↥F := finrank_map_mkQ Oth F hFO

end Formalism.MainNotions.N.Ln34.UniversalFiltration

end
