import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.PtStep0
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bridge

noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Matrix Formalism.UG Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.PairingIndexBounds.F
open scoped TensorProduct

namespace Formalism.MainNotions.G.KAat

variable {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [StarRing E] [Algebra F E] {sp : Spaces R F E} {N : ℕ}

def mvL (γ : GL (Fin N) E) (Λ : Submodule (𝓞 E) (Fin N → E)) : Submodule (𝓞 E) (Fin N → E) :=
  Λ.map (((toLE γ : (Fin N → E) ≃ₗ[E] (Fin N → E)) : (Fin N → E) →ₗ[E] (Fin N → E)).restrictScalars (𝓞 E))

theorem toLE_apply (γ : GL (Fin N) E) (x : Fin N → E) : toLE γ x = (γ : Matrix (Fin N) (Fin N) E) *ᵥ x := rfl

theorem toLE_inv_apply (γ : GL (Fin N) E) (x : Fin N → E) : toLE γ (toLE γ⁻¹ x) = x := by
  rw [toLE_apply, toLE_apply, Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]

theorem toLE_inv_apply' (γ : GL (Fin N) E) (x : Fin N → E) : toLE γ⁻¹ (toLE γ x) = x := by
  rw [toLE_apply, toLE_apply, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]

theorem bc_mulVec (γ : GL (Fin N) E) (x : Fin N → E) :
    ((bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) :
      Matrix (Fin N) (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) *ᵥ (fun a => inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (x a)) =
      fun a => inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (((γ : Matrix (Fin N) (Fin N) E) *ᵥ x) a) := by
  funext a
  simp [bc, Matrix.mulVec, dotProduct, map_sum, map_mul]

theorem latAd_rat (γ : GL (Fin N) E) (y : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (Lb : Submodule (𝓞 E) (Fin N → E)) :
    latAd (bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ * y) Lb = mvL γ (latAd y Lb) := by
  unfold latAd mvL
  rw [Submodule.map_span]
  congr 1
  set B := bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ with hB
  have h2 : ∀ v : Fin N → E ⊗[F] FiniteAdeleRing (𝓞 F) F, (B⁻¹ : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)).val *ᵥ (B.val *ᵥ v) = v := fun v => by
    rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
  have key : ∀ x : Fin N → E, ((B * y)⁻¹ : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)).val *ᵥ (fun a => inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (x a)) =
      (y⁻¹ : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)).val *ᵥ (fun a => inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (toLE γ⁻¹ x a)) := by
    intro x
    have h1 : (fun a => inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (x a)) = B.val *ᵥ (fun a => inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (toLE γ⁻¹ x a)) := by
      rw [hB, bc_mulVec, ← toLE_apply, toLE_inv_apply]
    rw [h1, _root_.mul_inv_rev, Units.val_mul, ← Matrix.mulVec_mulVec, h2]
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_image, LinearMap.coe_restrictScalars, LinearEquiv.coe_coe, key]
  constructor
  · intro hx
    exact ⟨toLE γ⁻¹ x, hx, toLE_inv_apply γ x⟩
  · rintro ⟨z, hz, rfl⟩
    rwa [toLE_inv_apply']

def HatStab (Lb : Submodule (𝓞 E) (Fin N → E)) (κ : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) : Prop :=
  ∀ z : Fin N → E ⊗[F] FiniteAdeleRing (𝓞 F) F,
    ((κ⁻¹ : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin N) (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) *ᵥ z ∈
      Formalism.L2.Herm.hatL (F := F) Lb ↔ z ∈ Formalism.L2.Herm.hatL (F := F) Lb

theorem latAd_stab (y κ : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (Lb : Submodule (𝓞 E) (Fin N → E)) (hκ : HatStab Lb κ) :
    latAd (y * κ) Lb = latAd y Lb := by
  unfold latAd
  congr 1
  ext x
  simp only [Set.mem_setOf_eq]
  rw [_root_.mul_inv_rev, Units.val_mul, ← Matrix.mulVec_mulVec]
  exact hκ _

private lemma hform_eq_lemma (σ : E →+* E) (J : Matrix (Fin N) (Fin N) E) (x y : Fin N → E) :
    hform σ J x y = (fun i => σ (x i)) ⬝ᵥ (J *ᵥ y) := by
  simp only [hform, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

private lemma ringHom_mulVec_eq_map_mulVec (σ : E →+* E) (M : Matrix (Fin N) (Fin N) E) (x : Fin N → E) :
    (fun i => σ ((M *ᵥ x) i)) = (M.map σ) *ᵥ (fun i => σ (x i)) := by
  funext i
  simp [Matrix.mulVec, dotProduct, map_sum, map_mul]

private lemma hform_mulVec_eq_of_cT_mul_mul_eq' (σ : E →+* E) (J : Matrix (Fin N) (Fin N) E) (M : Matrix (Fin N) (Fin N) E)
    (hM : cT σ M * J * M = J) (x y : Fin N → E) :
    hform σ J (M *ᵥ x) (M *ᵥ y) = hform σ J x y := by
  rw [hform_eq_lemma, hform_eq_lemma, ringHom_mulVec_eq_map_mulVec]
  unfold cT at hM
  rw [Matrix.mul_assoc] at hM
  conv_lhs => rw [dotProduct_comm, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, dotProduct_comm]
  simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc, hM]

theorem dualSet_mvL (σ : E →+* E) (J : Matrix (Fin N) (Fin N) E) (γ : GL (Fin N) E) (hγ : γ ∈ UJ σ J)
    (Λ : Submodule (𝓞 E) (Fin N → E)) : dualSet σ J (mvL γ Λ) = toLE γ '' dualSet σ J Λ := by
  have hM : cT σ (γ : Matrix (Fin N) (Fin N) E) * J * (γ : Matrix (Fin N) (Fin N) E) = J := hγ
  ext v
  unfold dualSet mvL
  simp only [Set.mem_setOf_eq, Set.mem_image, Submodule.mem_map, LinearMap.coe_restrictScalars, LinearEquiv.coe_coe]
  constructor
  · intro hv
    refine ⟨toLE γ⁻¹ v, fun x hx => ?_, toLE_inv_apply γ v⟩
    have h := hv (toLE γ x) ⟨x, hx, rfl⟩
    rw [← hform_mulVec_eq_of_cT_mul_mul_eq' σ J _ hM x (toLE γ⁻¹ v), ← toLE_apply, ← toLE_apply, toLE_inv_apply]
    exact h
  · rintro ⟨w, hw, rfl⟩ x ⟨x', hx', rfl⟩
    rw [toLE_apply, toLE_apply, hform_mulVec_eq_of_cT_mul_mul_eq' σ J _ hM]
    exact hw x' hx'

theorem compan_mvL (J : Matrix (Fin N) (Fin N) E) (a : 𝓞 E) (γ : GL (Fin N) E) (hγ : γ ∈ UJ (sp.cm.sig : E →+* E) J)
    (Λ : Submodule (𝓞 E) (Fin N → E)) : compan (sp := sp) J a (mvL γ Λ) = mvL γ (compan (sp := sp) J a Λ) := by
  unfold compan
  rw [dualSet_mvL _ J γ hγ Λ]
  unfold mvL
  simp only [Submodule.map_sup, Submodule.map_smul'', Submodule.map_span, LinearMap.coe_restrictScalars, LinearEquiv.coe_coe]

theorem toStd_mvL (σ : E →+* E) (J : Matrix (Fin N) (Fin N) E) (γ : GL (Fin N) E) (Λ : Submodule (𝓞 E) (Fin N → E)) :
    toStd σ J (mvL γ Λ) = (toStd σ J Λ).map
      (((stdG σ J γ : (Fin N → E) ≃ₗ[E] (Fin N → E)) : (Fin N → E) →ₗ[E] (Fin N → E)).restrictScalars (𝓞 E)) := by
  unfold toStd mvL stdG
  ext v
  simp only [Submodule.mem_map, LinearMap.coe_restrictScalars, LinearEquiv.coe_coe, LinearEquiv.trans_apply]
  constructor
  · rintro ⟨w, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨stdCo σ J x, ⟨x, hx, rfl⟩, by rw [LinearEquiv.symm_apply_apply]⟩
  · rintro ⟨w, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨toLE γ x, ⟨x, hx, rfl⟩, by rw [LinearEquiv.symm_apply_apply]⟩

def latK (sp : Spaces R F E) (J : Matrix (Fin N) (Fin N) E) (a : 𝓞 E) (y : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F))
    (Lb : Submodule (𝓞 E) (Fin N → E)) : Submodule (𝓞 E) (Fin N → E) :=
  toStd (sp.cm.sig : E →+* E) J (compan (sp := sp) J a (latAd y Lb))

theorem latK_tr (J : Matrix (Fin N) (Fin N) E) (a : 𝓞 E) (y κ₀ : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F))
    (Lb : Submodule (𝓞 E) (Fin N → E)) (γ₀ : GL (Fin N) E) (hγ : γ₀ ∈ UJ (sp.cm.sig : E →+* E) J) (hκ : HatStab Lb κ₀) :
    latK sp J a (bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ₀ * y * κ₀) Lb = (latK sp J a y Lb).map
      (((stdG (sp.cm.sig : E →+* E) J γ₀ : (Fin N → E) ≃ₗ[E] (Fin N → E)) : (Fin N → E) →ₗ[E] (Fin N → E)).restrictScalars (𝓞 E)) := by
  unfold latK
  rw [latAd_stab _ _ _ hκ, latAd_rat, compan_mvL J a γ₀ hγ, toStd_mvL]

theorem reE_rfl : reE (E := E) (rfl : N = N) = LinearEquiv.refl E (Fin N → E) := by
  ext x i
  simp [reE]

theorem map_reE_symm {n : ℕ} (h : N = n) (h' : n = N) (Λ : Submodule (𝓞 E) (Fin N → E)) :
    (Λ.map (((reE (E := E) h : (Fin N → E) ≃ₗ[E] (Fin n → E)) : (Fin N → E) →ₗ[E] (Fin n → E)).restrictScalars (𝓞 E))).map
      (((reE (E := E) h' : (Fin n → E) ≃ₗ[E] (Fin N → E)) : (Fin n → E) →ₗ[E] (Fin N → E)).restrictScalars (𝓞 E)) = Λ := by
  subst h
  have e : ∀ h'' : N = N, reE (E := E) h'' = LinearEquiv.refl E (Fin N → E) := fun _ => reE_rfl
  rw [e]
  ext x
  simp

theorem map_reE_rfl (h : N = N) (Λ : Submodule (𝓞 E) (Fin N → E)) :
    Λ.map (((reE (E := E) h : (Fin N → E) ≃ₗ[E] (Fin N → E)) : (Fin N → E) →ₗ[E] (Fin N → E)).restrictScalars (𝓞 E)) = Λ := by
  have e : reE (E := E) h = LinearEquiv.refl E (Fin N → E) := reE_rfl
  rw [e]
  ext x
  simp

end Formalism.MainNotions.G.KAat

end
