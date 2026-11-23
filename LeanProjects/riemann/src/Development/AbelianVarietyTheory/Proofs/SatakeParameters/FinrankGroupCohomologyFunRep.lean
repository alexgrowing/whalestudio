import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.BasicForm
import GroundTheory.ProfiniteCohomology.GlobalClassFormation.IdeleCohomology.Product

noncomputable section

open CategoryTheory
open scoped Matrix

namespace GlobalTheory.BorelCoh

def matVecRep {H : Type} [Group H] {d : ℕ} (ξ : H →* Matrix (Fin d) (Fin d) ℂ) : Representation ℂ H (Fin d → ℂ) :=
  (Matrix.toLinAlgEquiv' : Matrix (Fin d) (Fin d) ℂ ≃ₐ[ℂ] Module.End ℂ (Fin d → ℂ)).toRingEquiv.toMonoidHom.comp ξ

theorem matVecRep_apply {H : Type} [Group H] {d : ℕ} (ξ : H →* Matrix (Fin d) (Fin d) ℂ) (h : H) (v : Fin d → ℂ) :
    matVecRep ξ h v = ξ h *ᵥ v := by
  simp [matVecRep, Matrix.toLinAlgEquiv'_apply]

namespace Shapiro

variable {Γ Y : Type} [Group Γ] [MulAction Γ Y] {d : ℕ} (ξ : Γ →* Matrix (Fin d) (Fin d) ℂ)

abbrev stabRep (y : Y) : Rep ℂ (MulAction.stabilizer Γ y) :=
  Rep.of (matVecRep (ξ.comp (MulAction.stabilizer Γ y).subtype))

theorem xi_mulVec_inv (g : Γ) (v : Fin d → ℂ) : ξ g *ᵥ (ξ g⁻¹ *ᵥ v) = v := by
  rw [Matrix.mulVec_mulVec, ← map_mul, mul_inv_cancel, map_one, Matrix.one_mulVec]

def toCoindLin (y : Y) : (Y → Fin d → ℂ) →ₗ[ℂ]
    Representation.coindV (MulAction.stabilizer Γ y).subtype (stabRep ξ y).ρ where
  toFun f := ⟨fun h => ξ h *ᵥ f (h⁻¹ • y), fun s h => by
    have hs : (s : Γ)⁻¹ • y = y := by
      rw [inv_smul_eq_iff]; exact s.2.symm
    change ξ ((s : Γ) * h) *ᵥ f (((s : Γ) * h)⁻¹ • y) = matVecRep (ξ.comp (MulAction.stabilizer Γ y).subtype) s (ξ h *ᵥ f (h⁻¹ • y))
    rw [matVecRep_apply, mul_inv_rev, mul_smul, hs, map_mul, MonoidHom.comp_apply, Subgroup.coe_subtype,
      Matrix.mulVec_mulVec]⟩
  map_add' f f' := Subtype.ext (funext fun h => by simp [Matrix.mulVec_add])
  map_smul' c f := Subtype.ext (funext fun h => by simp [Matrix.mulVec_smul])

def toCoind (y : Y) : Rep.of (funRep Y ξ) ⟶ Rep.coind (MulAction.stabilizer Γ y).subtype (stabRep ξ y) :=
  Rep.ofHom
    { toLinearMap := toCoindLin ξ y
      isIntertwining' := fun γ => by
        ext f h i
        change (ξ h *ᵥ (ξ γ *ᵥ f (γ⁻¹ • h⁻¹ • y))) i = (ξ (h * γ) *ᵥ f ((h * γ)⁻¹ • y)) i
        rw [Matrix.mulVec_mulVec, ← map_mul, mul_inv_rev, mul_smul] }

theorem toCoind_pi_bijective {ι : Type} (y : ι → Y) (hcov : ∀ x : Y, ∃ j, ∃ g : Γ, g • y j = x)
    (hdis : ∀ i j (g : Γ), g • y i = y j → i = j) :
    Function.Bijective fun (f : Rep.of (funRep Y ξ)) (j : ι) => (toCoind ξ (y j)).hom f := by
  constructor
  · intro f f' hff
    funext x
    obtain ⟨j, g, rfl⟩ := hcov x
    have h1 := congrArg (fun F => F.1 g⁻¹) (congrFun hff j)
    change ξ g⁻¹ *ᵥ f (g⁻¹⁻¹ • y j) = ξ g⁻¹ *ᵥ f' (g⁻¹⁻¹ • y j) at h1
    rw [inv_inv] at h1
    rw [← xi_mulVec_inv ξ g (f (g • y j)), h1, xi_mulVec_inv]
  · intro F
    choose J G hJG using hcov
    refine ⟨fun x => ξ (G x) *ᵥ (F (J x)).1 (G x)⁻¹, funext fun j => Subtype.ext (funext fun h => ?_)⟩
    change ξ h *ᵥ (ξ (G (h⁻¹ • y j)) *ᵥ (F (J (h⁻¹ • y j))).1 (G (h⁻¹ • y j))⁻¹) = (F j).1 h
    have key : ∀ j' (g : Γ), g • y j' = h⁻¹ • y j → ξ h *ᵥ (ξ g *ᵥ (F j').1 g⁻¹) = (F j).1 h := by
      intro j' g hg
      have hst : (h * g) • y j' = y j := by rw [mul_smul, hg, smul_inv_smul]
      obtain rfl := hdis j' j (h * g) hst
      have hmem : h * g ∈ MulAction.stabilizer Γ (y j') := hst
      have hc := (F j').2 ⟨h * g, hmem⟩ g⁻¹
      change (F j').1 ((h * g) * g⁻¹) = matVecRep (ξ.comp (MulAction.stabilizer Γ (y j')).subtype) ⟨h * g, hmem⟩ ((F j').1 g⁻¹) at hc
      rw [mul_inv_cancel_right, matVecRep_apply, MonoidHom.comp_apply, Subgroup.coe_subtype] at hc
      rw [hc]
      change ξ h *ᵥ (ξ g *ᵥ _) = ξ (h * g) *ᵥ _
      rw [map_mul, Matrix.mulVec_mulVec]
    exact key _ _ (hJG _)

def cohEquiv {ι : Type} (y : ι → Y) (hcov : ∀ x : Y, ∃ j, ∃ g : Γ, g • y j = x)
    (hdis : ∀ i j (g : Γ), g • y i = y j → i = j) (q : ℕ) :
    groupCohomology (Rep.of (funRep Y ξ)) q ≃ₗ[ℂ]
      ∀ j, groupCohomology (Rep.of (matVecRep (ξ.comp (MulAction.stabilizer Γ (y j)).subtype))) q :=
  GroundTheory.ProfCoh.groupCohomologyPiEquiv (fun j => toCoind ξ (y j)) (toCoind_pi_bijective ξ y hcov hdis) q ≪≫ₗ
    LinearEquiv.piCongrRight fun j => (groupCohomology.coindIso (stabRep ξ (y j)) q).toLinearEquiv

end Shapiro

end GlobalTheory.BorelCoh
