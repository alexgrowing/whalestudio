import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.StabKset
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LatDict

noncomputable section

open scoped Classical TensorProduct
open Matrix NumberField

namespace Formalism.L2.SG.RhoPf

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.Pf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Ind

variable {D : D7} {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T)

theorem inv_apply' (δ : (VS D).V ≃ₗ[D.host.E] (VS D).V) (y : (VS D).V) : (δ⁻¹ : (VS D).V ≃ₗ[D.host.E] (VS D).V) y = δ.symm y :=
  rfl

theorem xa_top : F0.Xa D.R.rS = F0.X := by
  unfold FlagG.Xa FlagG.X
  congr 1
  ext x
  simp [Fin.is_lt]

theorem st_mul {γ δ : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hγ : γ ∈ stabF D F0) (hδ : δ ∈ stabF D F0) :
    γ * δ ∈ stabF D F0 := by
  refine ⟨mul_mem hγ.1 hδ.1, fun j => ?_, ?_⟩
  · rw [kmap_mul, hδ.2.1 j, hγ.2.1 j]
  · show γ (δ F0.z) = F0.z
    rw [hδ.2.2, hγ.2.2]

theorem st_inv {γ : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hγ : γ ∈ stabF D F0) : γ⁻¹ ∈ stabF D F0 := by
  refine ⟨inv_mem hγ.1, fun j => ?_, ?_⟩
  · conv_lhs => rw [← hγ.2.1 j]
    rw [← kmap_mul, inv_mul_cancel, kmap_one]
  · show γ.symm F0.z = F0.z
    conv_lhs => rw [← hγ.2.2]
    exact γ.symm_apply_apply _

theorem stab_X_mem {γ : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hγ : γ ∈ stabF D F0) {x : (VS D).V} (hx : x ∈ F0.X) :
    γ x ∈ F0.X := by
  rw [← xa_top] at hx ⊢
  rw [← hγ.2.1 D.R.rS]
  exact Submodule.mem_map_of_mem hx

theorem stab_perp_mem {γ : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hγ : γ ∈ stabF D F0) {y : (VS D).V}
    (hy : y ∈ perpS (VS D) F0.X) : γ y ∈ perpS (VS D) F0.X := by
  intro x hx
  have h1 := hy _ (stab_X_mem F0 (st_inv F0 hγ) hx)
  have h2 := hγ.1 (γ⁻¹ x) y
  rw [inv_apply', LinearEquiv.apply_symm_apply] at h2
  rw [h2]
  exact h1

def ind {γ : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hγ : γ ∈ stabF D F0) : WbQ D F0 → WbQ D F0 :=
  Submodule.mapQ (F0.X.comap (perpS (VS D) F0.X).subtype) (F0.X.comap (perpS (VS D) F0.X).subtype)
    ((γ : (VS D).V →ₗ[D.host.E] (VS D).V).restrict (fun y hy => stab_perp_mem F0 hγ hy))
    (fun x hx => stab_X_mem F0 hγ hx)

theorem ind_mk {γ : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hγ : γ ∈ stabF D F0) (x : perpS (VS D) F0.X) :
    ind F0 hγ (Submodule.Quotient.mk x) = Submodule.Quotient.mk ⟨γ x.1, stab_perp_mem F0 hγ x.2⟩ := rfl

theorem autLz_iff (Λ : Submodule (𝓞 D.host.E) (VS D).V) (φ : WbQ D F0 → WbQ D F0) :
    φ ∈ autLz D F0 Λ ↔ ∃ γ, ∃ hγ : γ ∈ stabF D F0, Formalism.HermitianLatticesTheory.gmap γ Λ = Λ ∧ φ = ind F0 hγ := by
  constructor
  · rintro ⟨γ, hγ, hΛ, hφ⟩
    refine ⟨γ, hγ, hΛ, funext fun q => ?_⟩
    refine Submodule.Quotient.induction_on _ q (fun x => ?_)
    exact (hφ x (stab_perp_mem F0 hγ x.2)).trans rfl
  · rintro ⟨γ, hγ, hΛ, rfl⟩
    exact ⟨γ, hγ, hΛ, fun x hx => rfl⟩

theorem ind_inv_cancel {δ : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hδ : δ ∈ stabF D F0) (q : WbQ D F0) :
    ind F0 (st_inv F0 hδ) (ind F0 hδ q) = q := by
  refine Submodule.Quotient.induction_on _ q (fun x => ?_)
  rw [ind_mk, ind_mk]
  congr 1
  apply Subtype.ext
  show δ⁻¹ (δ x.1) = x.1
  rw [inv_apply', LinearEquiv.symm_apply_apply]

theorem ind_cancel_inv {δ : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hδ : δ ∈ stabF D F0) (q : WbQ D F0) :
    ind F0 hδ (ind F0 (st_inv F0 hδ) q) = q := by
  refine Submodule.Quotient.induction_on _ q (fun x => ?_)
  rw [ind_mk, ind_mk]
  congr 1
  apply Subtype.ext
  show δ (δ⁻¹ x.1) = x.1
  rw [inv_apply', LinearEquiv.apply_symm_apply]

theorem card_autLz_gmap {δ : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hδ : δ ∈ stabF D F0)
    (Λ : Submodule (𝓞 D.host.E) (VS D).V) :
    Nat.card ↥(autLz D F0 (Formalism.HermitianLatticesTheory.gmap δ Λ)) = Nat.card ↥(autLz D F0 Λ) := by
  let c : (WbQ D F0 → WbQ D F0) → (WbQ D F0 → WbQ D F0) := fun φ => ind F0 hδ ∘ φ ∘ ind F0 (st_inv F0 hδ)
  have hc : Function.Injective c := by
    intro φ ψ hφψ
    funext q
    have h1 := congrFun hφψ (ind F0 hδ q)
    simp only [c, Function.comp, ind_inv_cancel] at h1
    have h2 := congrArg (ind F0 (st_inv F0 hδ)) h1
    rwa [ind_inv_cancel, ind_inv_cancel] at h2
  have hset : autLz D F0 (Formalism.HermitianLatticesTheory.gmap δ Λ) = c '' autLz D F0 Λ := by
    ext ψ
    rw [autLz_iff, Set.mem_image]
    constructor
    · rintro ⟨γ', hγ', hΛ', rfl⟩
      refine ⟨ind F0 (st_mul F0 (st_mul F0 (st_inv F0 hδ) hγ') hδ),
        (autLz_iff F0 Λ _).2 ⟨_, _, ?_, rfl⟩, ?_⟩
      · rw [gmap_mul', gmap_mul', hΛ', ← gmap_mul', inv_mul_cancel, gmap_one']
      · funext q
        refine Submodule.Quotient.induction_on _ q (fun x => ?_)
        simp only [c, Function.comp]
        rw [ind_mk, ind_mk, ind_mk, ind_mk]
        congr 1
        apply Subtype.ext
        show δ ((δ⁻¹ * γ' * δ) (δ⁻¹ x.1)) = γ' x.1
        show δ (δ⁻¹ (γ' (δ (δ⁻¹ x.1)))) = γ' x.1
        rw [inv_apply', inv_apply', LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
    · rintro ⟨φ, hφ, rfl⟩
      obtain ⟨γ, hγ, hΛ, rfl⟩ := (autLz_iff F0 Λ φ).1 hφ
      refine ⟨δ * γ * δ⁻¹, st_mul F0 (st_mul F0 hδ hγ) (st_inv F0 hδ), ?_, ?_⟩
      · rw [gmap_mul', ← gmap_mul' δ⁻¹ δ, inv_mul_cancel, gmap_one', gmap_mul', hΛ]
      · funext q
        refine Submodule.Quotient.induction_on _ q (fun x => rfl)
  rw [hset]
  exact Nat.card_image_of_injective hc _

end Ind

end Formalism.L2.SG.RhoPf
