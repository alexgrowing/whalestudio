import Mathlib
open scoped TensorProduct

namespace GlobalTheory

theorem exists_semilinear_descent_to_baseChange :
  ∀ {LL : Type} [Field LL] [Algebra ℚ LL] (L0 : IntermediateField ℚ LL) {Ks : Type} [Field Ks] [Algebra Ks LL]
    (kKs : Ks →+* L0), (∀ x, ((kKs x : L0) : LL) = algebraMap Ks LL x) →
    ∀ {WL : Type} [AddCommGroup WL] [Module LL WL] [Module Ks WL] [IsScalarTower Ks LL WL]
    (WK : Submodule Ks WL) {n : ℕ} (bs : Fin n → WL), (∀ i, bs i ∈ WK) →
    Submodule.span Ks (Set.range bs) = WK → LinearIndependent LL bs → Submodule.span LL (Set.range bs) = ⊤ →
    ∀ {KT : Type} [Field KT] [Algebra Ks KT] (rd : L0 →+* KT), (∀ s, algebraMap Ks KT s = rd (kKs s)) →
    ∃ Φ : WL →+ KT ⊗[Ks] WK, (∀ (c : L0) (x : WL), Φ ((c : LL) • x) = rd c • Φ x) ∧
      (∀ (f : WL →ₗ[LL] WL) (fr : WK →ₗ[Ks] WK), (∀ w : WK, (fr w : WL) = f w) →
        ∀ x, Φ (f x) = LinearMap.baseChange KT fr (Φ x)) ∧
      ∀ w : WK, Φ (w : WL) = (1 : KT) ⊗ₜ[Ks] w := by
  intro LL _ _ L0 Ks _ _ kKs hk WL _ _ _ _ WK n bs hb hKs hLi hLs KT _ _ rd hrd
  obtain ⟨π, hπ⟩ := LinearMap.exists_leftInverse_of_injective (Algebra.linearMap L0 LL)
    (LinearMap.ker_eq_bot.mpr (algebraMap L0 LL).injective)
  have hπ1 : π 1 = 1 := by
    have := LinearMap.congr_fun hπ 1
    simpa using this
  have hπx : ∀ (c : L0) (y : LL), π ((c : LL) * y) = c * π y := by
    intro c y
    have : ((c : LL) * y) = c • y := (Algebra.smul_def c y).symm
    rw [this, map_smul, smul_eq_mul]
  obtain ⟨B, hB⟩ : ∃ B : Module.Basis (Fin n) LL WL, ∀ k, B k = bs k :=
    ⟨Module.Basis.mk hLi (by rw [hLs]), fun k => Module.Basis.mk_apply _ _ k⟩
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : WL →+ KT ⊗[Ks] WK,
      ∀ x, Φ x = ∑ k, rd (π (B.repr x k)) • ((1 : KT) ⊗ₜ[Ks] (⟨bs k, hb k⟩ : WK)) :=
    ⟨{ toFun := fun x => ∑ k, rd (π (B.repr x k)) • ((1 : KT) ⊗ₜ[Ks] (⟨bs k, hb k⟩ : WK))
       map_zero' := by simp
       map_add' := by intro x y; simp [map_add, add_smul, Finset.sum_add_distrib] },
     fun _ => rfl⟩
  have key : ∀ (l : LL) (w : WK), Φ (l • (w : WL)) = rd (π l) • ((1 : KT) ⊗ₜ[Ks] w) := by
    intro l w
    obtain ⟨s, hs⟩ := (Submodule.mem_span_range_iff_exists_fun Ks).mp
      (show (w : WL) ∈ Submodule.span Ks (Set.range bs) by rw [hKs]; exact w.2)
    have hw : w = ∑ k, s k • (⟨bs k, hb k⟩ : WK) := by
      apply Subtype.ext; simp [hs]
    have hrep : ∀ k, B.repr (l • (w : WL)) k = l * algebraMap Ks LL (s k) := by
      have : l • (w : WL) = ∑ k, (l * algebraMap Ks LL (s k)) • B k := by
        rw [← hs, Finset.smul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [hB, mul_smul, algebraMap_smul]
      intro k
      rw [this, B.repr_sum_self]
    rw [hΦ]
    conv_rhs => rw [hw, TensorProduct.tmul_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hrep, ← hk, mul_comm, hπx, map_mul, ← hrd, TensorProduct.tmul_smul, ← algebraMap_smul KT (s k),
      smul_smul, mul_comm]
  refine ⟨Φ, ?_, ?_, ?_⟩
  · intro c x
    rw [hΦ, hΦ x, Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, Finsupp.smul_apply, smul_eq_mul, hπx, map_mul, mul_smul]
  · intro f fr hf x
    conv_lhs => rw [← B.sum_repr x]
    rw [map_sum, map_sum, hΦ x, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, hB, ← hf ⟨bs k, hb k⟩, key, map_smul, LinearMap.baseChange_tmul]
  · intro w
    have := key 1 w
    rw [one_smul, hπ1, map_one, one_smul] at this
    exact this

end GlobalTheory
