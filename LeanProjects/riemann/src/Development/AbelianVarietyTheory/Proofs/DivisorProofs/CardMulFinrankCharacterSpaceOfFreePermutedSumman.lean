import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ArithmeticCylinders GlobalTheory.BadCount Module

namespace GlobalTheory.BadCount

theorem trace_rho_eq_zero_of_free {K Γ V X : Type} [Field K] [Group Γ] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] [DecidableEq X] (ρ : Representation K Γ V) (H : Subgroup Γ)
    [MulAction H X] (hfree : ∀ (h : H) (x : X), h • x = x → h = 1)
    (A : X → Submodule K V) (hA : DirectSum.IsInternal A)
    (hmap : ∀ (h : H) (x : X), ∀ v ∈ A x, ρ h v ∈ A (h • x)) (h : H) (hne : h ≠ 1) :
    LinearMap.trace K V (ρ h) = 0 := by
  classical
  refine LinearMap.trace_eq_zero_of_mapsTo_ne hA (fun x => h • x) (fun x hx => hne (hfree h x hx)) ?_
  intro x v hv
  exact hmap h x v hv

theorem card_mul_finrank_eig_of_free : ∀ (K Γ V X : Type) [Field K] [CharZero K] [Group Γ] [Finite Γ] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Fintype X] [DecidableEq X] (ρ : Representation K Γ V) (H : Subgroup Γ) [MulAction H X], (∀ (h : H) (x : X), h • x = x → h = 1) → ∀ (A : X → Submodule K V), DirectSum.IsInternal A → (∀ (h : H) (x : X), ∀ v ∈ A x, ρ h v ∈ A (h • x)) → ∀ (Hb : Subgroup Γ), Hb ≤ H → ∀ lam : Hb →* Kˣ, Nat.card Hb * finrank K (eig ρ Hb lam) = finrank K V := by
  intro K Γ V X _ _ _ _ _ _ _ _ _ ρ H _ hfree A hA hmap Hb hle lam
  classical
  haveI : Fintype Hb := Fintype.ofFinite Hb
  set n : K := (Fintype.card Hb : K) with hn
  have hn0 : n ≠ 0 := by simp [hn, Fintype.card_ne_zero]
  let P : Module.End K V := n⁻¹ • ∑ h : Hb, (((lam h)⁻¹ : Kˣ) : K) • ρ h
  have hproj : LinearMap.IsProj (eig ρ Hb lam) P := by
    constructor
    · intro v
      rw [mem_eig]
      intro g
      simp only [P, LinearMap.smul_apply, LinearMap.sum_apply, map_smul, map_sum]
      rw [smul_comm]
      congr 1
      rw [Finset.smul_sum]
      refine Fintype.sum_equiv (Equiv.mulLeft g) _ _ (fun h => ?_)
      simp only [Equiv.coe_mulLeft, Subgroup.coe_mul, map_mul, Module.End.mul_apply, smul_smul, mul_inv, Units.val_mul]
      congr 1
      simp only [← Units.val_mul]
      congr 1
      group
    · intro v hv
      rw [mem_eig] at hv
      simp only [P, LinearMap.smul_apply, LinearMap.sum_apply, hv, smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul, Finset.sum_const, Finset.card_univ]
      rw [← Nat.cast_smul_eq_nsmul K, smul_smul, ← hn, inv_mul_cancel₀ hn0, one_smul]
  have htr : LinearMap.trace K V P = n⁻¹ * (finrank K V : K) := by
    simp only [P, map_smul, map_sum, smul_eq_mul]
    congr 1
    rw [Finset.sum_eq_single 1]
    · simp [LinearMap.trace_one]
    · intro h _ hne
      have h0 : LinearMap.trace K V (ρ h) = 0 :=
        trace_rho_eq_zero_of_free ρ H hfree A hA hmap ⟨h, hle h.2⟩ (by
          intro e; apply hne; ext; simpa using congrArg Subtype.val e)
      rw [h0, mul_zero]
    · simp
  have h1 := hproj.trace
  rw [htr] at h1
  rw [Nat.card_eq_fintype_card]
  have : ((Fintype.card Hb * finrank K (eig ρ Hb lam) : ℕ) : K) = (finrank K V : K) := by
    push_cast
    rw [← h1, ← hn, ← mul_assoc, mul_inv_cancel₀ hn0, one_mul]
  exact_mod_cast this

end GlobalTheory.BadCount
