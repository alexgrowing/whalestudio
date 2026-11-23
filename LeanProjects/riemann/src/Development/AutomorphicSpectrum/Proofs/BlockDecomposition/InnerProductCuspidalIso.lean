import Mathlib
import Development.WeilBound.CoreStatements.FiniteTypeHarishChandra.SupportExistsAll
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GreenLabelSurjective.Transp
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PermutationMatrixPropertiesStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SimpleIffIrreducibleStatement

open Polynomial CategoryTheory
open Formalism.IrreducibleCountingLemmas.TYPES hiding zIdem IsCuspidal
open ReciprocityTheory.Ty.Fin

noncomputable section

namespace GlobalTheory.CompanionTheory.TyFin.IpIso

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
variable {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

theorem glEquiv_symm_symm (e : α ≃ β) (g : GL α K) :
    (glEquiv K e.symm).symm g = glEquiv K e g := by
  apply Units.ext
  ext i j
  rw [PI.GreenLabelSurjWork.glEquiv_symm_val, PI.GreenLabelSurjWork.glEquiv_val]
  simp

theorem glEquiv_conj (e e' : α ≃ β) (g : GL α K) :
    glEquiv K e' g =
      pm K (e.symm.trans e') * glEquiv K e g * (pm K (e.symm.trans e'))⁻¹ := by
  rw [(GlobalTheory.T.permutation_matrix_properties K β (e.symm.trans e')).2.1]
  apply Units.ext
  ext i j
  rw [PI.GreenLabelSurjWork.glEquiv_val, PI.GreenLabelSurjWork.glEquiv_val,
    PI.GreenLabelSurjWork.glEquiv_val]
  simp

theorem along_of_along (lam : FDRep ℂ (GL α K)) (mu : FDRep ℂ (GL β K)) (e e' : α ≃ β)
    (φ : lam ≃ₗ[ℂ] mu) (h : ∀ g x, φ (lam.ρ g x) = mu.ρ (glEquiv K e' g) (φ x)) :
    ∃ ψ : lam ≃ₗ[ℂ] mu, ∀ g x, ψ (lam.ρ g x) = mu.ρ (glEquiv K e g) (ψ x) := by
  set P : GL β K := pm K (e.symm.trans e') with hP
  let m : (mu : Type) ≃ₗ[ℂ] (mu : Type) := LinearEquiv.ofLinear (mu.ρ P⁻¹) (mu.ρ P)
    (by rw [← Module.End.mul_eq_comp, ← map_mul]; simp; rfl)
    (by rw [← Module.End.mul_eq_comp, ← map_mul]; simp; rfl)
  refine ⟨φ.trans m, fun g x => ?_⟩
  have hm : ∀ y, m y = mu.ρ P⁻¹ y := fun _ => rfl
  simp only [LinearEquiv.trans_apply, hm]
  rw [h, glEquiv_conj e e' g, ← hP]
  have : P⁻¹ * (P * glEquiv K e g * P⁻¹) = glEquiv K e g * P⁻¹ := by group
  rw [← Module.End.mul_apply, ← map_mul, this, map_mul, Module.End.mul_apply]

theorem cuspIso_iff_along (lam : FDRep ℂ (GL α K)) (mu : FDRep ℂ (GL β K)) (e : α ≃ β) :
    CuspIso K lam mu ↔
      ∃ φ : lam ≃ₗ[ℂ] mu, ∀ g x, φ (lam.ρ g x) = mu.ρ (glEquiv K e g) (φ x) := by
  constructor
  · rintro ⟨e', φ, h⟩
    exact along_of_along lam mu e e' φ h
  · rintro ⟨φ, h⟩
    exact ⟨e, φ, h⟩

theorem iso_transp_symm_iff (lam : FDRep ℂ (GL α K)) (mu : FDRep ℂ (GL β K)) (e : α ≃ β) :
    Nonempty (lam ≅ transp e.symm mu) ↔
      ∃ φ : lam ≃ₗ[ℂ] mu, ∀ g x, φ (lam.ρ g x) = mu.ρ (glEquiv K e g) (φ x) := by
  rw [GlobalTheory.T.simple_iff_irreducible.2 (GL α K) lam (transp e.symm mu)]
  constructor
  · rintro ⟨ε, h⟩
    refine ⟨ε, fun g x => ?_⟩
    have := h g x
    rw [PI.GreenLabelSurjWork.transp_ρ, glEquiv_symm_symm] at this
    exact this
  · rintro ⟨φ, h⟩
    refine ⟨φ, fun g x => ?_⟩
    rw [PI.GreenLabelSurjWork.transp_ρ, glEquiv_symm_symm]
    exact h g x

theorem iso_transp_iff (lam : FDRep ℂ (GL α K)) (mu : FDRep ℂ (GL β K)) (e : α ≃ β) :
    Nonempty (transp e lam ≅ mu) ↔
      ∃ φ : lam ≃ₗ[ℂ] mu, ∀ g x, φ (lam.ρ g x) = mu.ρ (glEquiv K e g) (φ x) := by
  rw [GlobalTheory.T.simple_iff_irreducible.2 (GL β K) (transp e lam) mu]
  constructor
  · rintro ⟨ε, h⟩
    refine ⟨ε, fun g x => ?_⟩
    have := h (glEquiv K e g) x
    rw [PI.GreenLabelSurjWork.transp_ρ, MulEquiv.symm_apply_apply] at this
    exact this
  · rintro ⟨φ, h⟩
    refine ⟨φ, fun γ x => ?_⟩
    rw [PI.GreenLabelSurjWork.transp_ρ]
    have := h ((glEquiv K e).symm γ) x
    rw [MulEquiv.apply_symm_apply] at this
    exact this

theorem ip_char (lam : FDRep ℂ (GL α K)) (mu : FDRep ℂ (GL β K)) (e : α ≃ β)
    (hl : Simple lam) (hm : Simple mu) :
    ip Set.univ lam.character (fun x => mu.character (glEquiv K e x)) =
      (open Classical in if CuspIso K lam mu then 1 else 0) := by
  classical
  have hT : Simple (transp e.symm mu) := PI.GreenLabelSurjWork.transp_simple e.symm mu hm
  have hc : ∀ g, mu.character (glEquiv K e g) = (transp e.symm mu).character g := by
    intro g
    show _ = LinearMap.trace ℂ _ ((transp e.symm mu).ρ g)
    rw [PI.GreenLabelSurjWork.transp_ρ, glEquiv_symm_symm]
    rfl
  haveI : Invertible (Nat.card (GL α K) : ℂ) := invertibleOfNonzero (by
    exact_mod_cast Nat.card_pos.ne')
  have ho := FDRep.char_orthonormal (transp e.symm mu) lam
  have hiff : CuspIso K lam mu ↔ Nonempty (transp e.symm mu ≅ lam) := by
    rw [cuspIso_iff_along lam mu e, ← iso_transp_symm_iff lam mu e]
    exact ⟨fun ⟨i⟩ => ⟨i.symm⟩, fun ⟨i⟩ => ⟨i.symm⟩⟩
  simp only [ip, Set.ncard_univ, Set.mem_univ, if_true, hc]
  simp only [mul_comm (lam.character _)]
  rw [ho]
  simp only [hiff]

theorem main : ReciprocityTheory.Ty.Fin.St.IpCuspIso := by
  intro K _ _ _ α β _ _ _ _ lam mu e hl hm
  refine ⟨ip_char lam mu e hl hm, ?_⟩
  rw [cuspIso_iff_along lam mu e, iso_transp_iff lam mu e]

end GlobalTheory.CompanionTheory.TyFin.IpIso
