import Formalism.WachLatticeTwists.HodgeTateChains.FrobeniusPowerCongruence
import Formalism.WachLatticeTwists.HodgeTateChains.HodgeTateFiltrations.H2KilledByTateDuality
import Formalism.WachLatticeTwists.HodgeTateChains.HodgeTateFiltrations.FiltPow

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic

theorem idealStep : StatIdealStep := by
  intro A _ I σ h0 h1 a
  induction a with
  | zero => intro r _; rw [zero_add, pow_one]; exact h0 r
  | succ a ih =>
    intro r hr
    rw [pow_succ] at hr
    refine Submodule.mul_induction_on hr ?_ ?_
    · intro x hx y hy
      have e : σ (x * y) - x * y = (σ x - x) * σ y + x * (σ y - y) := by rw [map_mul]; ring
      rw [e]
      apply Ideal.add_mem
      · rw [pow_succ I (a + 1)]
        refine Ideal.mul_mem_mul (ih x hx) ?_
        have : σ y = y + (σ y - y) := by ring
        rw [this]
        exact I.add_mem hy (Ideal.pow_le_self (by norm_num) (h1 y hy))
      · have e2 : a + 1 + 1 = a + 2 := rfl
        rw [e2, pow_add]
        exact Ideal.mul_mem_mul hx (h1 y hy)
    · intro x y hx hy
      have e : σ (x + y) - (x + y) = (σ x - x) + (σ y - y) := by rw [map_add]; ring
      rw [e]
      exact Ideal.add_mem _ hx hy

theorem filtStep : StatFiltStep := by
  intro A _ I σ N _ _ γ hsl hσ hW3 a x hx
  refine Submodule.smul_induction_on hx ?_ ?_
  · intro r hr n _
    have e : γ (r • n) - r • n = (σ r - r) • γ n + r • (γ n - n) := by
      rw [hsl, sub_smul, smul_sub]; abel
    rw [e]
    apply Submodule.add_mem
    · exact Submodule.smul_mem_smul (hσ a r hr) trivial
    · have h := Submodule.smul_mem_smul hr (hW3 n)
      rw [← Submodule.smul_assoc, smul_eq_mul, ← pow_succ] at h
      exact h
  · intro x y hx hy
    have e : γ (x + y) - (x + y) = (γ x - x) + (γ y - y) := by rw [map_add]; abel
    rw [e]
    exact Submodule.add_mem _ hx hy

theorem frobenius_power_congruence_holds : FrobeniusPowerCongruence := by
  intro ℓ hℓ A _ I σ N _ _ γ hsl h0 h1 hW3 b hb x
  have hstep := filtStep A I σ N γ hsl (idealStep A I σ h0 h1) hW3
  exact filtPow ℓ hℓ N (fun a => (I ^ a • (⊤ : Submodule A N)).toAddSubgroup) γ
    (by simp) (fun a => by
      intro v hv
      have hv' : v ∈ I ^ (a + 1) • (⊤ : Submodule A N) := hv
      exact (Submodule.smul_mono_left (Ideal.pow_le_pow_right (Nat.le_succ a)) hv' :
        v ∈ I ^ a • (⊤ : Submodule A N)))
    (fun a v hv => hstep a v hv) b hb x

theorem freeK : StatFreeK := by
  intro ℓ _ H1K H1m H0m H0KQ H0mQ H1mQ _ _ _ _ _ _ _ _ _ _ _ _ res cup a0 a1 r0 cupQ al hc hinj htf hF y z hyz
  obtain ⟨zm, t, hz⟩ := hF (res y)
  refine ⟨zm, ?_⟩
  have h1 := congrArg a1 hz
  rw [map_smul, map_sub, map_smul, hyz, hc, map_zero, ← map_smul, ← map_sub] at h1
  have h2 := tf_pow htf t _ h1
  have h3 : ((ℓ : ℤ_[ℓ]) ^ al) • r0 z - a0 zm = 0 := hinj (by rw [h2, map_zero])
  exact (sub_eq_zero.1 h3).symm

end Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic
