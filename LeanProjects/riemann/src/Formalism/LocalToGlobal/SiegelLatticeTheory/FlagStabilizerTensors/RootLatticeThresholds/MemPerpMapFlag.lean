import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.WittFlags

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.PackageTie2

namespace Formalism.L2.SG.Pf.WittFlags

attribute [local instance] Formalism.BasicNotions.Host.cmStar
section Flag

variable {D : D7} {T : D.host.E} (β : (VS D).V ≃ₗ[D.host.E] (VS D).V) (hβ : β ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT)

theorem mapFlag_inv (F0 : FlagG (VS D) D.R.rS T) :
    Formalism.L2.SG.Saturated.mapFlag β⁻¹ (inv_mem hβ) (Formalism.L2.SG.Saturated.mapFlag β hβ F0) = F0 := by
  have key : ∀ x, (β⁻¹ : (VS D).V ≃ₗ[D.host.E] (VS D).V) (β x) = x := fun x => β.symm_apply_apply x
  cases F0
  simp only [Formalism.L2.SG.Saturated.mapFlag, key]
  all_goals rfl

theorem stabF_conj (F0 : FlagG (VS D) D.R.rS T) {γ : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hγ : γ ∈ stabF D F0) :
    β * γ * β⁻¹ ∈ stabF D (Formalism.L2.SG.Saturated.mapFlag β hβ F0) := by
  simp only [stabF] at hγ ⊢
  obtain ⟨h1, h2, h3⟩ := hγ
  have hXa : ∀ j, (Formalism.L2.SG.Saturated.mapFlag β hβ F0).Xa j =
      (F0.Xa j).map (β : (VS D).V →ₗ[D.host.E] (VS D).V) := by
    intro j
    first
      | rfl
      | (simp only [FlagG.Xa, Formalism.L2.SG.Saturated.mapFlag, Submodule.map_span, ← Set.range_comp]; rfl)
      | (simp only [FlagG.Xa, Formalism.L2.SG.Saturated.mapFlag, Submodule.map_span, Set.image_image]; rfl)
      | simp [FlagG.Xa, Formalism.L2.SG.Saturated.mapFlag, Submodule.map_span, Set.image_image, ← Set.range_comp]
  have hc : ((β * γ * β⁻¹ : (VS D).V ≃ₗ[D.host.E] (VS D).V) : (VS D).V →ₗ[D.host.E] (VS D).V).comp
      (β : (VS D).V →ₗ[D.host.E] (VS D).V) =
      (β : (VS D).V →ₗ[D.host.E] (VS D).V).comp (γ : (VS D).V →ₗ[D.host.E] (VS D).V) := by
    ext x
    show β (γ (β.symm (β x))) = β (γ x)
    rw [β.symm_apply_apply]
  refine ⟨mul_mem (mul_mem hβ h1) (inv_mem hβ), fun j => ?_, ?_⟩
  · rw [hXa j, ← Submodule.map_comp, hc, Submodule.map_comp, h2 j]
  · show β (γ (β.symm (β F0.z))) = β F0.z
    rw [β.symm_apply_apply, h3]

theorem stabF_conj_inv (F0 : FlagG (VS D) D.R.rS T) {γ : (VS D).V ≃ₗ[D.host.E] (VS D).V}
    (hγ : γ ∈ stabF D (Formalism.L2.SG.Saturated.mapFlag β hβ F0)) : β⁻¹ * γ * β ∈ stabF D F0 := by
  have h := stabF_conj β⁻¹ (inv_mem hβ) (Formalism.L2.SG.Saturated.mapFlag β hβ F0) hγ
  rwa [mapFlag_inv, inv_inv] at h

end Flag

theorem RowRepsIso_holds (D : D7) : Formalism.L2.SG.TermTieOf.RowRepsIso D := by
  have hL := LatIso_holds D
  intro β hβ T F0 what₂ hR
  obtain ⟨hrow, huniq⟩ := hR
  refine ⟨?_, ?_⟩
  · intro Λ hΛ
    obtain ⟨Λ0, h0, rfl⟩ := Finset.mem_image.1 hΛ
    exact Formalism.L2.SG.TermTieOf.rowLat_map hL β hβ F0 Λ0 (hrow Λ0 h0)
  · intro Λ hΛ
    have h0 : IsRowLat D F0 (Formalism.HermitianLatticesTheory.gmap β⁻¹ Λ) := by
      have h := Formalism.L2.SG.TermTieOf.rowLat_map hL β⁻¹ (inv_mem hβ) (Formalism.L2.SG.Saturated.mapFlag β hβ F0) Λ hΛ
      rw [mapFlag_inv] at h
      exact h
    obtain ⟨M, ⟨hM, γ, hγ, hγM⟩, hU⟩ := huniq _ h0
    refine ⟨Formalism.HermitianLatticesTheory.gmap β M, ⟨Finset.mem_image_of_mem _ hM, β * γ * β⁻¹, stabF_conj β hβ F0 hγ, ?_⟩, ?_⟩
    · rw [gmap_mul, gmap_mul, gmap_inv_gmap, hγM, gmap_gmap_inv]
    · rintro N ⟨hN, γ', hγ', hγN⟩
      obtain ⟨M', hM', rfl⟩ := Finset.mem_image.1 hN
      have hM'M : M' = M := by
        refine hU M' ⟨hM', β⁻¹ * γ' * β, stabF_conj_inv β hβ F0 hγ', ?_⟩
        rw [gmap_mul, gmap_mul, hγN]
      rw [hM'M]

section Wb

variable {D : D7} {T : D.host.E} (β : (VS D).V ≃ₗ[D.host.E] (VS D).V) (hβ : β ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT)
  (F0 : FlagG (VS D) D.R.rS T)

theorem perp_mapFlag :
    perpS (VS D) (Formalism.L2.SG.Saturated.mapFlag β hβ F0).X =
      (perpS (VS D) F0.X).map (β : (VS D).V →ₗ[D.host.E] (VS D).V) := by
  have hb : ∀ x y, (VS D).hT (β x) (β y) = (VS D).hT x y := by
    intro x y
    first
      | exact hβ x y
      | exact LinearMap.congr_fun₂ hβ x y
      | exact Formalism.HermitianLatticesTheory.isom_apply hβ x y
      | exact Formalism.L2.SG.Saturated.isom_apply hβ x y
      | exact isom_apply hβ x y
  have hX : (Formalism.L2.SG.Saturated.mapFlag β hβ F0).X = F0.X.map (β : (VS D).V →ₗ[D.host.E] (VS D).V) := by
    first
      | rfl
      | (simp only [FlagG.X, Formalism.L2.SG.Saturated.mapFlag, Submodule.map_span, ← Set.range_comp]; rfl)
      | (simp only [FlagG.X, Formalism.L2.SG.Saturated.mapFlag, Submodule.map_span, Set.image_union,
          Set.image_singleton, ← Set.range_comp]; rfl)
      | simp [FlagG.X, Formalism.L2.SG.Saturated.mapFlag, Submodule.map_span, ← Set.range_comp, Set.image_union]
  ext y
  rw [hX, Submodule.mem_map_equiv]
  simp only [perpS, Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk, Set.mem_setOf_eq]
  constructor
  · intro h x hx
    have h1 := h (β x) (Submodule.mem_map_of_mem hx)
    rwa [← β.apply_symm_apply y, hb] at h1
  · intro h x hx
    obtain ⟨x', hx', rfl⟩ := Submodule.mem_map.mp hx
    have h2 := hb x' (β.symm y)
    rw [β.apply_symm_apply] at h2
    exact h2.trans (h x' hx')

theorem mem_perp_mapFlag {y : (VS D).V} :
    y ∈ perpS (VS D) (Formalism.L2.SG.Saturated.mapFlag β hβ F0).X ↔ β.symm y ∈ perpS (VS D) F0.X := by
  rw [perp_mapFlag β hβ F0, Submodule.mem_map_equiv]

def perpEq : ↥(perpS (VS D) F0.X) ≃ₗ[D.host.E] ↥(perpS (VS D) (Formalism.L2.SG.Saturated.mapFlag β hβ F0).X) :=
  LinearEquiv.ofSubmodules β _ _ (perp_mapFlag β hβ F0).symm

theorem perpEq_map :
    Submodule.map (perpEq β hβ F0 : ↥(perpS (VS D) F0.X) →ₗ[D.host.E] ↥(perpS (VS D) (Formalism.L2.SG.Saturated.mapFlag β hβ F0).X))
      (F0.X.comap (perpS (VS D) F0.X).subtype) =
      (Formalism.L2.SG.Saturated.mapFlag β hβ F0).X.comap
        (perpS (VS D) (Formalism.L2.SG.Saturated.mapFlag β hβ F0).X).subtype := by
  ext ⟨y, hy⟩
  rw [Submodule.mem_map, Submodule.mem_comap, Submodule.subtype_apply]
  constructor
  · rintro ⟨x, hxX, hfx⟩
    rw [Submodule.mem_comap, Submodule.subtype_apply] at hxX
    show y ∈ _
    rw [Formalism.L2.SG.Pf.X_mapFlag β hβ F0, Submodule.mem_map]
    exact ⟨x.1, hxX, congrArg Subtype.val hfx⟩
  · intro hyX
    have hyX' : y ∈ F0.X.map (β : (VS D).V →ₗ[D.host.E] (VS D).V) := by
      rw [← Formalism.L2.SG.Pf.X_mapFlag β hβ F0]; exact hyX
    obtain ⟨x, hxX, rfl⟩ := (Submodule.mem_map).1 hyX'
    have hx0 : x ∈ perpS (VS D) F0.X := by
      have h := (mem_perp_mapFlag β hβ F0).1 hy
      have e : β.symm ((β : (VS D).V →ₗ[D.host.E] (VS D).V) x) = x := β.symm_apply_apply x
      rwa [e] at h
    exact ⟨⟨x, hx0⟩, hxX, Subtype.ext rfl⟩

def wbEquiv : WbQ D F0 ≃ WbQ D (Formalism.L2.SG.Saturated.mapFlag β hβ F0) :=
  (Submodule.Quotient.equiv _ _ (perpEq β hβ F0) (perpEq_map β hβ F0)).toEquiv

theorem wbEquiv_mk (x : ↥(perpS (VS D) F0.X)) :
    wbEquiv β hβ F0 (Submodule.Quotient.mk x) = Submodule.Quotient.mk (perpEq β hβ F0 x) := rfl

theorem autLz_fwd {Λ : Submodule (𝓞 D.host.E) (VS D).V} {φ : WbQ D F0 → WbQ D F0} (hφ : φ ∈ autLz D F0 Λ) :
    (wbEquiv β hβ F0) ∘ φ ∘ (wbEquiv β hβ F0).symm ∈
      autLz D (Formalism.L2.SG.Saturated.mapFlag β hβ F0) (Formalism.HermitianLatticesTheory.gmap β Λ) := by
  obtain ⟨γ, hγ, hΛ, hφ⟩ := hφ
  refine ⟨β * γ * β⁻¹, stabF_conj β hβ F0 hγ, ?_, ?_⟩
  · rw [gmap_mul, gmap_mul, gmap_inv_gmap, hΛ]
  · intro x hx
    have hy0 : β.symm x.1 ∈ perpS (VS D) F0.X := (mem_perp_mapFlag β hβ F0).1 x.2
    have hy1 : γ (β.symm x.1) ∈ perpS (VS D) F0.X := by
      have h := (mem_perp_mapFlag β hβ F0).1 hx
      have key : β.symm ((β * γ * β⁻¹) x.1) = γ (β.symm x.1) := by
        show β.symm (β (γ (β.symm x.1))) = _
        exact β.symm_apply_apply _
      rwa [key] at h
    have e1 : (wbEquiv β hβ F0).symm (Submodule.Quotient.mk x) = Submodule.Quotient.mk ⟨β.symm x.1, hy0⟩ := by
      rw [Equiv.symm_apply_eq, wbEquiv_mk]
      congr 1
      exact Subtype.ext (β.apply_symm_apply x.1).symm
    simp only [Function.comp_apply]
    rw [e1, hφ ⟨β.symm x.1, hy0⟩ hy1, wbEquiv_mk]
    congr 1

theorem autLz_bwd {Λ : Submodule (𝓞 D.host.E) (VS D).V}
    {ψ : WbQ D (Formalism.L2.SG.Saturated.mapFlag β hβ F0) → WbQ D (Formalism.L2.SG.Saturated.mapFlag β hβ F0)}
    (hψ : ψ ∈ autLz D (Formalism.L2.SG.Saturated.mapFlag β hβ F0) (Formalism.HermitianLatticesTheory.gmap β Λ)) :
    (wbEquiv β hβ F0).symm ∘ ψ ∘ (wbEquiv β hβ F0) ∈ autLz D F0 Λ := by
  obtain ⟨γ, hγ, hΛ, hψ⟩ := hψ
  refine ⟨β⁻¹ * γ * β, stabF_conj_inv β hβ F0 hγ, ?_, ?_⟩
  · rw [gmap_mul, gmap_mul, hΛ, gmap_inv_gmap]
  · intro x hx
    have hx1 : γ (β x.1) ∈ perpS (VS D) (Formalism.L2.SG.Saturated.mapFlag β hβ F0).X := by
      rw [mem_perp_mapFlag β hβ F0]
      exact hx
    simp only [Function.comp_apply]
    rw [wbEquiv_mk, Equiv.symm_apply_eq, hψ (perpEq β hβ F0 x) hx1, wbEquiv_mk]
    congr 1
    exact Subtype.ext (show γ (β x.1) = β (β.symm (γ (β x.1))) from (β.apply_symm_apply _).symm)

def autEquiv (Λ : Submodule (𝓞 D.host.E) (VS D).V) :
    autLz D F0 Λ ≃ autLz D (Formalism.L2.SG.Saturated.mapFlag β hβ F0) (Formalism.HermitianLatticesTheory.gmap β Λ) where
  toFun φ := ⟨_, autLz_fwd β hβ F0 φ.2⟩
  invFun ψ := ⟨_, autLz_bwd β hβ F0 ψ.2⟩
  left_inv φ := Subtype.ext (funext fun x => by simp)
  right_inv ψ := Subtype.ext (funext fun x => by simp)

end Wb

theorem WRowIso_holds (D : D7) : Formalism.L2.SG.TermTieOf.WRowIso D := by
  intro β hβ T F0 Λ
  simp only [Formalism.MainNotions.S.wRow]
  rw [Nat.card_congr (autEquiv β hβ F0 Λ).symm]

end Formalism.L2.SG.Pf.WittFlags
