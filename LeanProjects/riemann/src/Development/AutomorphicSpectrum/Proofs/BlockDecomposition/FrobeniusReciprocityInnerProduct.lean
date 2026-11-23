import Mathlib
import Development.WeilBound.CoreStatements.FiniteTypeHarishChandra.SupportExistsAll

open ReciprocityTheory.Ty.Fin

namespace GlobalTheory.CompanionTheory.TyFin

theorem sum_sum_conj {Γ : Type} [Group Γ] [Fintype Γ] (f : Γ → ℂ) :
    ∑ g, ∑ x, f (x * g * x⁻¹) = (Fintype.card Γ : ℂ) * ∑ h, f h := by
  rw [Finset.sum_comm]
  have h : ∀ x : Γ, ∑ g, f (x * g * x⁻¹) = ∑ h, f h := fun x =>
    Fintype.sum_equiv (MulAut.conj x).toEquiv _ _ (fun g => by simp [MulAut.conj_apply])
  simp [h, Finset.card_univ]

theorem frobIp : ReciprocityTheory.Ty.Fin.St.FrobIp := by
  intro Γ _ _ A a c hc
  classical
  have hne : (Fintype.card Γ : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hU : ((Set.univ : Set Γ).ncard : ℂ) = (Fintype.card Γ : ℂ) := by
    rw [Set.ncard_univ, Nat.card_eq_fintype_card]
  have hA : ((A : Set Γ).ncard : ℂ) = (Nat.card A : ℂ) := by
    rw [← Nat.card_coe_set_eq]; rfl
  have hinv : ∀ h : Γ, h⁻¹ ∈ A ↔ h ∈ A := fun h => inv_mem_iff
  have hcx : ∀ x g : Γ, c (x * g * x⁻¹) = c g := hc
  constructor
  · have key : ∀ g x : Γ, (if x * g⁻¹ * x⁻¹ ∈ A then a (x * g⁻¹ * x⁻¹) else 0) * c g =
        (fun h => if h ∈ A then a h⁻¹ * c h else 0) (x * g * x⁻¹) := by
      intro g x
      have e : x * g⁻¹ * x⁻¹ = (x * g * x⁻¹)⁻¹ := by group
      simp only [e, hinv, hcx]
      split_ifs <;> simp
    have S : ∑ g, ((Nat.card A : ℂ)⁻¹ *
          ∑ x, if x * g⁻¹ * x⁻¹ ∈ A then a (x * g⁻¹ * x⁻¹) else 0) * c g =
        (Nat.card A : ℂ)⁻¹ * ((Fintype.card Γ : ℂ) * ∑ h, if h ∈ A then a h⁻¹ * c h else 0) := by
      rw [← sum_sum_conj, Finset.mul_sum]
      refine Finset.sum_congr rfl fun g _ => ?_
      rw [mul_assoc, Finset.sum_mul]
      exact congrArg _ (Finset.sum_congr rfl fun x _ => key g x)
    simp only [ip, indF, Set.mem_univ, if_true, SetLike.mem_coe, hU, hA]
    rw [S]
    field_simp
  · have key : ∀ g x : Γ, c g⁻¹ * (if x * g * x⁻¹ ∈ A then a (x * g * x⁻¹) else 0) =
        (fun h => if h ∈ A then c h⁻¹ * a h else 0) (x * g * x⁻¹) := by
      intro g x
      have e : (x * g * x⁻¹)⁻¹ = x * g⁻¹ * x⁻¹ := by group
      simp only [e, hcx]
      split_ifs <;> simp
    have S : ∑ g, c g⁻¹ * ((Nat.card A : ℂ)⁻¹ *
          ∑ x, if x * g * x⁻¹ ∈ A then a (x * g * x⁻¹) else 0) =
        (Nat.card A : ℂ)⁻¹ * ((Fintype.card Γ : ℂ) * ∑ h, if h ∈ A then c h⁻¹ * a h else 0) := by
      rw [← sum_sum_conj, Finset.mul_sum]
      refine Finset.sum_congr rfl fun g _ => ?_
      rw [mul_left_comm, Finset.mul_sum]
      exact congrArg _ (Finset.sum_congr rfl fun x _ => key g x)
    simp only [ip, indF, Set.mem_univ, if_true, SetLike.mem_coe, hU, hA]
    rw [S]
    field_simp

end GlobalTheory.CompanionTheory.TyFin
