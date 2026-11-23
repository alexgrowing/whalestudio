import Mathlib

namespace GlobalTheory

theorem index_smul_cocycle_eq_coboundary (R G X : Type) [CommRing R] [Group G] [AddCommGroup X]
    [Module R X] (ρ : Representation R G X) (H : Subgroup G) [H.FiniteIndex] (f : G → X)
    (hf : ∀ g h, f (g * h) = f g + ρ g (f h)) (hH : ∃ x, ∀ h ∈ H, f h = ρ h x - x) :
    ∃ x, ∀ g, H.index • f g = ρ g x - x := by
  classical
  obtain ⟨x₀, hx₀⟩ := hH
  haveI : Fintype (G ⧸ H) := Fintype.ofFinite _
  set f' : G → X := fun g => f g - (ρ g x₀ - x₀) with hf'
  have hc : ∀ g h, f' (g * h) = f' g + ρ g (f' h) := by
    intro g h
    simp only [hf', hf, map_mul, Module.End.mul_apply, map_sub]
    abel
  have hz : ∀ h ∈ H, f' h = 0 := by
    intro h hh
    simp only [hf', hx₀ h hh, sub_self]
  have hq : ∀ (g : G) (q : G ⧸ H), f' (g • q).out = f' g + ρ g (f' q.out) := by
    intro g q
    have h1 : ((g * q.out : G) : G ⧸ H) = ((g • q).out : G ⧸ H) := by
      rw [QuotientGroup.out_eq', ← smul_eq_mul, MulAction.Quotient.mk_smul_out]
    have h2 := QuotientGroup.eq.mp h1
    have h3 : (g • q).out = (g * q.out) * ((g * q.out)⁻¹ * (g • q).out) := by group
    rw [h3, hc, hz _ h2, map_zero, add_zero, hc]
  refine ⟨H.index • x₀ - ∑ q : G ⧸ H, f' q.out, fun g => ?_⟩
  have hs : ∑ q : G ⧸ H, f' (g • q).out = ∑ q : G ⧸ H, f' q.out :=
    Equiv.sum_comp (MulAction.toPerm g) (fun q : G ⧸ H => f' q.out)
  simp only [hq, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ] at hs
  rw [← map_sum, ← Nat.card_eq_fintype_card, ← Subgroup.index_eq_card] at hs
  have hfg : f g = f' g + (ρ g x₀ - x₀) := by simp [hf']
  have hs' : H.index • f' g = ∑ q : G ⧸ H, f' q.out - ρ g (∑ q : G ⧸ H, f' q.out) :=
    eq_sub_of_add_eq hs
  rw [hfg, smul_add, hs', map_sub, map_nsmul, smul_sub]
  abel

end GlobalTheory
