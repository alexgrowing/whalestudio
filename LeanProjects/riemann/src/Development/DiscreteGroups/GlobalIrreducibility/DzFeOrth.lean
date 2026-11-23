import Mathlib

noncomputable section

namespace DiscreteGroups.sglob.DzFe

variable {g : ℕ} [Fact g.Prime]

def psiC (ψ₀ : AddChar (ZMod g) Circle) : AddChar (ZMod g) ℂ where
  toFun x := (ψ₀ x : ℂ)
  map_zero_eq_one' := by simp
  map_add_eq_mul' a b := by simp [AddChar.map_add_eq_mul]

theorem psiC_apply (ψ₀ : AddChar (ZMod g) Circle) (x : ZMod g) : psiC ψ₀ x = (ψ₀ x : ℂ) := rfl

theorem sum_psi_mul (ψ₀ : AddChar (ZMod g) Circle) (hψ : ψ₀ ≠ 1) (c : ZMod g) :
    ∑ t : ZMod g, (ψ₀ (t * c) : ℂ) = if c = 0 then (g : ℂ) else 0 := by
  split_ifs with hc
  · subst hc; simp [ZMod.card]
  · obtain ⟨s, hs⟩ : ∃ s, ψ₀ s ≠ 1 := by
      by_contra h
      push Not at h
      exact hψ (by ext s; rw [h s, AddChar.one_apply])
    have key : (ψ₀ s : ℂ) * ∑ t : ZMod g, (ψ₀ (t * c) : ℂ) = ∑ t : ZMod g, (ψ₀ (t * c) : ℂ) := by
      rw [Finset.mul_sum]
      refine Fintype.sum_equiv (Equiv.addRight (s * c⁻¹)) _ _ (fun t => ?_)
      rw [Equiv.coe_addRight, add_mul, mul_assoc, inv_mul_cancel₀ hc, mul_one, AddChar.map_add_eq_mul,
        Circle.coe_mul, mul_comm]
    have hs' : (ψ₀ s : ℂ) ≠ 1 := fun h => hs (Circle.ext (by simpa using h))
    have : ((ψ₀ s : ℂ) - 1) * ∑ t : ZMod g, (ψ₀ (t * c) : ℂ) = 0 := by rw [sub_mul, key, one_mul, sub_self]
    exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hs')

theorem sum_pi_psi (ψ₀ : AddChar (ZMod g) Circle) (hψ : ψ₀ ≠ 1) {ι : Type} [Fintype ι] [DecidableEq ι]
    (c : ι → ZMod g) :
    ∑ f : ι → ZMod g, (ψ₀ (∑ i, f i * c i) : ℂ) = if c = 0 then (g : ℂ) ^ Fintype.card ι else 0 := by
  have h1 : ∀ f : ι → ZMod g, (ψ₀ (∑ i, f i * c i) : ℂ) = ∏ i, (ψ₀ (f i * c i) : ℂ) := fun f => by
    have hs : ∀ s : Finset ι, psiC ψ₀ (∑ i ∈ s, f i * c i) = ∏ i ∈ s, psiC ψ₀ (f i * c i) := by
      intro s
      induction s using Finset.induction_on with
      | empty => simp [AddChar.map_zero_eq_one]
      | insert a s ha ih => rw [Finset.sum_insert ha, AddChar.map_add_eq_mul, ih, Finset.prod_insert ha]
    exact hs Finset.univ
  simp_rw [h1]
  rw [← Fintype.prod_sum (fun i t => (ψ₀ (t * c i) : ℂ))]
  simp_rw [sum_psi_mul ψ₀ hψ]
  split_ifs with hc
  · subst hc
    simp
  · obtain ⟨i, hi⟩ : ∃ i, c i ≠ 0 := by
      by_contra h
      push Not at h
      exact hc (funext h)
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])

end DiscreteGroups.sglob.DzFe
