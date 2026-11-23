import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RealCusp

noncomputable section

open NumberField IsDedekindDomain Matrix Neutral.B1 GlobalTheory.CuspRep Formalism.L2.Host

namespace UpperTheory.V.Af

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {a : ℕ}

def IsInvTOf (π π' : TR.CuspSub F a) : Prop :=
  ∃ e : π.V ≃ₗ[ℂ] π'.V, (∀ k φ, π'.op (.fin k) (e φ) = e (π.op (.fin (invT a (Af F) k)) φ)) ∧
    (∀ k φ, π'.op (.cpt k) (e φ) = e (π.op (.cpt k) φ)) ∧
    ∀ X φ, π'.op (.lie X) (e φ) = e (π.op (.lie (TR.toL (-(Matrix.of X)ᵀ))) φ)

def IsTwistOf (π : TR.CuspSub F a) (χ : HChar F) (π' : TR.CuspSub F a) : Prop :=
  ∃ (e : π.V ≃ₗ[ℂ] π'.V) (d : TR.Rinf F →ₗ[ℝ] ℂ),
    (∀ (z : TR.Rinf F) (u : (TR.Rinf F)ˣ), (∀ v, u.val v = Real.exp (z v)) →
      ((χ.1 (TR.infId F u) : ℂˣ) : ℂ) = Complex.exp (d z)) ∧
    (∀ k φ, π'.op (.fin k) (e φ) = ((chiDet a χ (finGL F a k) : ℂˣ) : ℂ) • e (π.op (.fin k) φ)) ∧
    (∀ k φ, π'.op (.cpt k) (e φ) =
      ((chiDet a χ (TR.infGL F a (Unitary.toUnits k)) : ℂˣ) : ℂ) • e (π.op (.cpt k) φ)) ∧
    ∀ X φ, π'.op (.lie X) (e φ) = e (π.op (.lie X) φ) + d (Matrix.of X).trace • e φ

theorem isSelfDualBy_of_iso {π π₁ π₂ : TR.CuspSub F a} {χ : HChar F} (B : π.V →ₗ[ℂ] π.V →ₗ[ℂ] ℂ)
    (hl : ∀ φ, (∀ ψ, B φ ψ = 0) → φ = 0) (hr : ∀ ψ, (∀ φ, B φ ψ = 0) → ψ = 0)
    (hf : ∀ k φ ψ, B (π.op (.fin k) φ) (π.op (.fin (invT a (Af F) k)) ψ) = B φ ψ)
    (hc : ∀ k φ ψ, B (π.op (.cpt k) φ) (π.op (.cpt k) ψ) = B φ ψ)
    (hX : ∀ X φ ψ, B (π.op (.lie X) φ) ψ + B φ (π.op (.lie (TR.toL (-(Matrix.of X)ᵀ))) ψ) = 0)
    (h₁ : IsInvTOf π π₁) (h₂ : IsTwistOf π₁ χ π₂) (h : π.Iso π₂) : π.IsSelfDualBy χ := by
  obtain ⟨e₁, f₁, c₁, x₁⟩ := h₁
  obtain ⟨e₂, d, hd, f₂, c₂, x₂⟩ := h₂
  obtain ⟨T, hT⟩ := h
  let S : π.V ≃ₗ[ℂ] π.V := (e₁.trans e₂).trans T.symm
  have hS : ∀ ψ, T (S ψ) = e₂ (e₁ ψ) := fun ψ => T.apply_symm_apply _
  refine ⟨B.compl₂ S.symm.toLinearMap, d, fun φ h => hl φ fun ψ => ?_, fun ψ h => ?_, hd, fun k φ ψ => ?_,
    fun k φ ψ => ?_, fun X φ ψ => ?_⟩
  · simpa using h (S ψ)
  · exact S.symm.map_eq_zero_iff.1 (hr _ h)
  · obtain ⟨ψ, rfl⟩ := S.surjective ψ
    have e : π.op (.fin k) (S ψ) = S (((chiDet a χ (finGL F a k) : ℂˣ) : ℂ) • π.op (.fin (invT a (Af F) k)) ψ) :=
      T.injective (by rw [hT, hS, hS, f₂, f₁, map_smul, map_smul])
    simp [e, hf]
  · obtain ⟨ψ, rfl⟩ := S.surjective ψ
    have e : π.op (.cpt k) (S ψ) =
        S (((chiDet a χ (TR.infGL F a (Unitary.toUnits k)) : ℂˣ) : ℂ) • π.op (.cpt k) ψ) :=
      T.injective (by rw [hT, hS, hS, c₂, c₁, map_smul, map_smul])
    simp [e, hc]
  · obtain ⟨ψ, rfl⟩ := S.surjective ψ
    have e : π.op (.lie X) (S ψ) = S (π.op (.lie (TR.toL (-(Matrix.of X)ᵀ))) ψ + d (Matrix.of X).trace • ψ) :=
      T.injective (by rw [hT, hS, hS, x₂, x₁, map_add, map_add, map_smul, map_smul])
    have := hX X φ ψ
    simp only [e, LinearMap.compl₂_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply, map_add, map_smul, smul_eq_mul]
    linear_combination this

end UpperTheory.V.Af
