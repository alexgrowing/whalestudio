import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.CosetTrace
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsSurjHomZmodOfIsPGroupStatement

open GlobalTheory.AlmostEt
open scoped NNReal

namespace GlobalTheory.AlmostEt

theorem exists_lagrange_resolvent : ∀ (L : Type) [Field L] (p : ℕ), p.Prime → ∀ (G : Type) [Group G]
    [MulSemiringAction G L] [Finite G] [Nontrivial G] [FaithfulSMul G L], IsPGroup p G →
    ∀ ζ : L, IsPrimitiveRoot ζ p → (∀ g : G, g • ζ = ζ) →
    ∃ (σ : G) (α : L), α ≠ 0 ∧ σ • α = ζ * α ∧ ∀ g : G, g • α ^ p = α ^ p := by
  intro L _ p hp G _ _ _ _ _ hG ζ hζ hfix
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact (1 < p) := ⟨hp.one_lt⟩
  classical
  letI : Fintype G := Fintype.ofFinite G
  obtain ⟨χ, hχ⟩ := GlobalTheory.T.exists_surjective_hom_zmod_of_isPGroup p G hG
  set ψ : G → L := fun g => ζ ^ (Multiplicative.toAdd (χ g)).val with hψdef
  have hζp : ζ ^ p = 1 := hζ.pow_eq_one
  have hmod : ∀ n : ℕ, ζ ^ n = ζ ^ (n % p) := fun n => by
    conv_lhs => rw [← Nat.div_add_mod n p, pow_add, pow_mul, hζp, one_pow, one_mul]
  have hψmul : ∀ a b, ψ (a * b) = ψ a * ψ b := by
    intro a b
    simp only [hψdef, map_mul, toAdd_mul, ZMod.val_add, ← pow_add]
    exact (hmod _).symm
  have hψp : ∀ g, ψ g ^ p = 1 := by
    intro g; simp only [hψdef]; rw [← pow_mul, mul_comm, pow_mul, hζp, one_pow]
  have hψne : ∀ g, ψ g ≠ 0 := fun g h => by
    have := hψp g; rw [h, zero_pow hp.ne_zero] at this; exact zero_ne_one this
  have hψfix : ∀ g h : G, g • ψ h = ψ h := fun g h => by simp only [hψdef, smul_pow', hfix]
  let f : G → (L →* L) := fun g => (MulSemiringAction.toRingHom G L g : L →* L)
  have hf : Function.Injective f := by
    intro g h hgh
    apply FaithfulSMul.eq_of_smul_eq_smul (α := L)
    intro x
    exact DFunLike.congr_fun hgh x
  have hli : LinearIndependent L (fun g : G => ((f g : L →* L) : L → L)) :=
    (linearIndependent_monoidHom L L).comp f hf
  have hex : ∃ x : L, ∑ g : G, ψ g⁻¹ * (g • x) ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    have h0 : ∑ g : G, ψ g⁻¹ • ((f g : L →* L) : L → L) = 0 := by
      funext x
      simpa [f, Finset.sum_apply] using hcon x
    exact hψne _ ((Fintype.linearIndependent_iff.mp hli) (fun g => ψ g⁻¹) h0 1)
  obtain ⟨x, hx⟩ := hex
  set α := ∑ g : G, ψ g⁻¹ * (g • x) with hα
  have hact : ∀ h : G, h • α = ψ h * α := by
    intro h
    rw [hα, Finset.smul_sum, Finset.mul_sum]
    simp only [smul_mul', hψfix, smul_smul]
    refine Fintype.sum_equiv (Equiv.mulLeft h) _ _ (fun g => ?_)
    simp only [Equiv.coe_mulLeft]
    have e : ψ h * ψ h⁻¹ = 1 := by
      rw [← hψmul, mul_inv_cancel]; simp [hψdef]
    rw [mul_inv_rev, hψmul g⁻¹ h⁻¹]
    linear_combination (-(ψ g⁻¹ * ((h * g) • x))) * e
  obtain ⟨σ, hσ⟩ := hχ (Multiplicative.ofAdd 1)
  refine ⟨σ, α, hx, ?_, ?_⟩
  · rw [hact σ]
    congr 1
    simp [hψdef, hσ, ZMod.val_one]
  · intro g
    rw [smul_pow', hact g, mul_pow, hψp, one_mul]

end GlobalTheory.AlmostEt
