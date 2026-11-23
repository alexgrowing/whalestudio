import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

noncomputable section

namespace GlobalTheory.BalExt

variable {O : Type} [CommRing O] (bar : O → O) (X : Type) [AddCommGroup X] [Module O X]

theorem finite_bilinForm [Module.Finite ℤ X] : Module.Finite ℤ (LinearMap.BilinForm ℤ X) := by
  obtain ⟨n, g, hg⟩ := Module.Finite.exists_fin' ℤ X
  let e : LinearMap.BilinForm ℤ X →ₗ[ℤ] LinearMap.BilinForm ℤ (Fin n → ℤ) :=
    { toFun := fun β => β.compl₁₂ g g
      map_add' := fun β γ => by ext; simp
      map_smul' := fun c β => by ext; simp }
  refine Module.Finite.of_injective e fun β γ h => ?_
  ext x y
  obtain ⟨x', rfl⟩ := hg x
  obtain ⟨y', rfl⟩ := hg y
  exact LinearMap.congr_fun₂ h x' y'

theorem isTorsionFree_quot :
    Module.IsTorsionFree ℤ (LinearMap.BilinForm ℤ X ⧸ balForms bar X) := by
  refine Module.IsTorsionFree.of_smul_eq_zero fun k q h => ?_
  by_cases hk : k = 0
  · exact Or.inl hk
  refine Or.inr ?_
  induction q using Submodule.Quotient.induction_on with
  | H β =>
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at h
  rw [Submodule.Quotient.mk_eq_zero]
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun y z => ?_, fun a y z => ?_⟩
  · have := h1 y z
    simp only [LinearMap.smul_apply, smul_eq_mul] at this
    exact mul_left_cancel₀ hk this
  · have := h2 a y z
    simp only [LinearMap.smul_apply, smul_eq_mul] at this
    exact mul_left_cancel₀ hk this

theorem exists_linearForm_ext {O : Type} [CommRing O] (bar : O → O) (X : Type) [AddCommGroup X] [Module O X]
    [Module.Finite ℤ X] (m : ℕ)
    (γ : Fin m → LinearMap.BilinForm ℤ X) (hγ : ∀ i, γ i ∈ GlobalTheory.PolFan.balForms bar X)
    (hb : GlobalTheory.Toroidal.IsPartOfBasis (fun i => (⟨γ i, hγ i⟩ : GlobalTheory.PolFan.balForms bar X)))
    (w : Fin m → ℤ) : ∃ ℓ : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ, ∀ i, ℓ (γ i) = w i := by
  classical
  haveI := finite_bilinForm X
  haveI := isTorsionFree_quot bar X
  haveI : Module.Free ℤ (LinearMap.BilinForm ℤ X ⧸ balForms bar X) := Module.free_of_finite_type_torsion_free'
  obtain ⟨s, hs⟩ := Module.projective_lifting_property (balForms bar X).mkQ LinearMap.id
    (Submodule.mkQ_surjective _)
  have hs' : ∀ q, (balForms bar X).mkQ (s q) = q := fun q => LinearMap.congr_fun hs q
  let r : LinearMap.BilinForm ℤ X →ₗ[ℤ] balForms bar X :=
    { toFun := fun β => ⟨β - s ((balForms bar X).mkQ β), by
        rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply, map_sub, hs', sub_self]⟩
      map_add' := fun β γ => by ext1; simp only [map_add, Submodule.coe_add]; abel
      map_smul' := fun c β => by ext1; simp [smul_sub] }
  obtain ⟨n, b, hbb⟩ := hb
  refine ⟨(b.constr ℤ (Sum.elim w 0)).comp r, fun i => ?_⟩
  have hr : r (γ i) = ⟨γ i, hγ i⟩ := by
    ext1
    show γ i - s ((balForms bar X).mkQ (γ i)) = γ i
    rw [Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero _).2 (hγ i), map_zero, sub_zero]
  have hbi : b (Sum.inl i) = ⟨γ i, hγ i⟩ := hbb i
  rw [LinearMap.comp_apply, hr, ← hbi, Module.Basis.constr_basis]
  rfl

end GlobalTheory.BalExt
