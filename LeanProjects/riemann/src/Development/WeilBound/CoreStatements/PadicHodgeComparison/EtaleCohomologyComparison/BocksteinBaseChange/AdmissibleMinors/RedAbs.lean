import Mathlib

namespace CrystallineSemistableComparison.Inj

theorem dual_span {k V : Type*} [Field k] [AddCommGroup V] [Module k V] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : ι → Module.Dual k V) (hf : ∀ v, (∀ i, f i v = 0) → v = 0) (g : Module.Dual k V) :
    ∃ c : ι → k, ∀ v, g v = ∑ i, c i * f i v := by
  have hker : LinearMap.ker (LinearMap.pi f) = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro v hv
    exact hf v fun i => congrFun hv i
  obtain ⟨ρ, hρ⟩ := LinearMap.exists_leftInverse_of_injective (LinearMap.pi f) hker
  refine ⟨fun i => g (ρ (Pi.single i 1)), fun v => ?_⟩
  have h1 : v = ρ (LinearMap.pi f v) := by rw [← LinearMap.comp_apply, hρ, LinearMap.id_apply]
  have h2 : LinearMap.pi f v = ∑ i, f i v • Pi.single i (1 : k) := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [h1, h2]
  simp [map_sum, mul_comm]

theorem red_abs {k B V : Type*} [Field k] [CommRing B] [AddCommGroup V] [Module k V] (q : k →+* B) (S : AddSubgroup B)
    (hS : ∀ x s, s ∈ S → q x * s ∈ S) {ι : Type*} [Fintype ι] (f : ι → Module.Dual k V)
    (hf : ∀ v, (∀ i, f i v = 0) → v = 0) {n : ℕ} (b : Module.Basis (Fin n) k V) (z : Fin n → B)
    (hy : ∀ i, ∑ m, z m * q (f i (b m)) ∈ S) (m' : Fin n) : z m' ∈ S := by
  classical
  obtain ⟨c, hc⟩ := dual_span f hf (b.coord m')
  have key : z m' = ∑ i, q (c i) * ∑ m, z m * q (f i (b m)) := by
    calc z m' = ∑ m, z m * q (b.coord m' (b m)) := by
          simp [Module.Basis.coord_apply, Finsupp.single_apply]
      _ = ∑ m, z m * q (∑ i, c i * f i (b m)) := by simp_rw [← hc]
      _ = _ := by
          simp_rw [map_sum, map_mul, Finset.mul_sum]
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun m _ => by ring
  rw [key]
  exact sum_mem fun i _ => hS _ _ (hy i)

end CrystallineSemistableComparison.Inj
