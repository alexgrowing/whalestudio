import Mathlib
import Formalism.PeriodIntegrals.KerIso
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.DeterminantKernelFiniteness.ExistsNatMulMemFracFam
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.DeterminantKernelFiniteness.ValuationLeOneOfDenom

noncomputable section
open scoped BigOperators
open NumberField

namespace PI.KerDetFinW

open PI.KerIso

lemma exists_denom_forward {K E : Type} [Field K] [NumberField K] [Field E] [NumberField E] [Algebra K E]
    {n : Type} [Fintype n] (I : FractionalIdeal (nonZeroDivisors (𝓞 E)) E)
    (g₀ : (Fin 4 → E) ≃ₗ[K] (Fin 4 × n → K)) :
    ∃ N : ℕ, 0 < N ∧ ∀ x : Fin 4 → E, (∀ a, x a ∈ I) → ∀ w,
      (N : K) * g₀ x w ∈ (algebraMap (𝓞 K) K).range := by
  obtain ⟨α, hα, hαI⟩ := I.isFractional
  have hα0 : algebraMap (𝓞 E) E α ≠ 0 := by
    intro h
    exact nonZeroDivisors.ne_zero hα
      ((map_eq_zero_iff _ (IsFractionRing.injective (𝓞 E) E)).1 h)
  let b := RingOfIntegers.basis E
  let φ : Fin 4 → Fin 4 × n → (E →ₗ[K] K) := fun a w =>
    LinearMap.proj w ∘ₗ (g₀ : (Fin 4 → E) →ₗ[K] (Fin 4 × n → K)) ∘ₗ
      LinearMap.single K (fun _ : Fin 4 => E) a
  obtain ⟨N, hN0, hN⟩ := exists_nat_mul_mem_int_fam
    (fun q : Fin 4 × Module.Free.ChooseBasisIndex ℤ (𝓞 E) × (Fin 4 × n) =>
      φ q.1 q.2.2 ((algebraMap (𝓞 E) E α)⁻¹ * algebraMap (𝓞 E) E (b q.2.1)))
  refine ⟨N, hN0, fun x hx w => ?_⟩
  have hxs : g₀ x w = ∑ a, φ a w (x a) := by
    conv_lhs => rw [← Finset.univ_sum_single x]
    rw [map_sum, Finset.sum_apply]
    rfl
  have hterm : ∀ a, (N : K) * φ a w (x a) ∈ (algebraMap (𝓞 K) K).range := by
    intro a
    obtain ⟨z, hz⟩ := hαI (x a) (FractionalIdeal.mem_coe.2 (hx a))
    have hxa : x a = ∑ i, (b.repr z i) • ((algebraMap (𝓞 E) E α)⁻¹ * algebraMap (𝓞 E) E (b i)) := by
      have h1 : x a = (algebraMap (𝓞 E) E α)⁻¹ * algebraMap (𝓞 E) E z := by
        rw [hz, Algebra.smul_def, inv_mul_cancel_left₀ hα0]
      rw [h1]
      conv_lhs => rw [← b.sum_repr z]
      rw [map_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_zsmul, mul_smul_comm]
    rw [hxa, map_sum, Finset.mul_sum]
    refine Subring.sum_mem _ fun i _ => ?_
    rw [map_zsmul, mul_smul_comm]
    exact zsmul_mem (hN (a, i, w)) _
  rw [hxs, Finset.mul_sum]
  exact Subring.sum_mem _ fun a _ => hterm a

lemma exists_denom_backward {K E : Type} [Field K] [NumberField K] [Field E] [NumberField E] [Algebra K E]
    {n : Type} [Fintype n] (I : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (hI : I ≠ 0)
    (g₀ : (Fin 4 → E) ≃ₗ[K] (Fin 4 × n → K)) :
    ∃ N : ℕ, 0 < N ∧ ∀ v : Fin 4 × n → K, (∀ w, v w ∈ (algebraMap (𝓞 K) K).range) → ∀ a,
      (N : E) * g₀.symm v a ∈ I := by
  classical
  obtain ⟨N, hN0, hN⟩ := exists_nat_mul_mem_frac_fam I hI
    (fun q : (Fin 4 × n) × Fin 4 => g₀.symm (Pi.single q.1 1) q.2)
  refine ⟨N, hN0, fun v hv a => ?_⟩
  have hv' : g₀.symm v = ∑ w, v w • g₀.symm (Pi.single w 1) := by
    conv_lhs => rw [← Finset.univ_sum_single v]
    rw [map_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [← map_smul]
    congr 1
    ext j
    rw [Pi.single_apply, Pi.smul_apply, Pi.single_apply]
    split_ifs <;> simp
  rw [hv', Finset.sum_apply, Finset.mul_sum, ← FractionalIdeal.mem_coe]
  refine Submodule.sum_mem _ fun w _ => ?_
  rw [FractionalIdeal.mem_coe, Pi.smul_apply, Algebra.smul_def, mul_left_comm]
  exact int_mul_mem I (hv w) (hN (w, a))

theorem detOrdFin : DetOrdFin := by
  intro K E _ _ _ _ _ n _ I hI S pp gp g₀ hpp hgp
  obtain ⟨N₁, h1pos, h1⟩ := exists_denom_forward (K := K) I g₀
  obtain ⟨N₂, h2pos, h2⟩ := exists_denom_backward I hI g₀
  have hg₀ : ∀ p, p.Prime → ¬ p ∣ N₁ * N₂ → AtP {x : E | x ∈ I} g₀ p := by
    intro p hp hdvd
    have hcop : Nat.Coprime (N₁ * N₂) p := ((Nat.Prime.coprime_iff_not_dvd hp).2 hdvd).symm
    exact ⟨fun x hx => ⟨N₁, Nat.Coprime.coprime_dvd_left (dvd_mul_right N₁ N₂) hcop, h1 x hx⟩,
      fun v hv => ⟨N₂, Nat.Coprime.coprime_dvd_left (dvd_mul_left N₂ N₁) hcop, h2 v hv⟩⟩
  refine (Nat.divisors (N₁ * N₂)).finite_toSet.subset ?_
  rintro p ⟨hp, hS, hne⟩
  rw [Finset.mem_coe, Nat.mem_divisors]
  refine ⟨?_, (Nat.mul_pos h1pos h2pos).ne'⟩
  by_contra hdvd
  exact hne (ordK_detRel_eq_zero (pp p) (hpp p hp hS) (hg₀ p hp hdvd) (hgp p hp hS))

end PI.KerDetFinW
