import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.SameNormBasic

open CategoryTheory AlgebraicGeometry TensorProduct
open UpperTheory.Gal.crystallineComparison

theorem UpperTheory.Gal.crystallineComparison.countIn_of :
    CountIn := by
  intro k H _ _ _ _ C hC
  have key : ∀ D : Submodule k H, Module.finrank k D
      = Module.finrank k (Submodule.map C.mkQ D) + Module.finrank k ↥(D ⊓ C) := by
    intro D
    have h := (C.mkQ.domRestrict D).finrank_range_add_finrank_ker
    rw [LinearMap.range_domRestrict, LinearMap.ker_domRestrict, Submodule.ker_mkQ] at h
    rw [← h, ← Submodule.finrank_map_subtype_eq, Submodule.map_comap_subtype]
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · rintro ⟨D₁, h₁⟩ ⟨D₂, h₂⟩ h
    simp only at h
    have e₁ := Submodule.comap_map_mkQ C D₁
    have e₂ := Submodule.comap_map_mkQ C D₂
    rw [h, e₂, sup_eq_right.mpr h₂] at e₁
    rw [sup_eq_right.mpr h₁] at e₁
    exact Subtype.ext e₁.symm
  · intro E
    refine ⟨⟨Submodule.comap C.mkQ E, ?_⟩, ?_⟩
    · intro x hx
      simp [Submodule.mem_comap, (Submodule.Quotient.mk_eq_zero C).mpr hx]
    · exact Submodule.map_comap_eq_self (by simp [Submodule.range_mkQ])
  · intro D hD
    rw [key D, inf_eq_right.mpr hD, hC]
  · intro D hD
    have hle : Module.finrank k ↥(D ⊓ C) ≤ 1 := hC ▸ Submodule.finrank_mono inf_le_right
    have hne : Module.finrank k ↥(D ⊓ C) ≠ 1 := by
      intro h1
      apply hD
      have := Submodule.eq_of_le_of_finrank_eq (inf_le_right : D ⊓ C ≤ C) (h1.trans hC.symm)
      exact this ▸ inf_le_left
    rw [key D]
    omega
