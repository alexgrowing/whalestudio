import Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.SmulNeZeroLat

open NumberField Matrix UpperTheory.V UpperTheory.V.KT
open scoped ComplexOrder

theorem UpperTheory.V.KT.spanpsd :
    ∀ (L : Type) [Field L] [NumberField L] (N : ℕ) (M : Set (Lat L N)),
    (∀ k ∈ Psd L N, (∀ y ∈ M, q k y = 0) → k = 0) → Spans M := by
  intro L _ _ N M hM
  classical
  by_contra hS
  have hlt : spanL M < ⊤ := lt_top_iff_ne_top.mpr hS
  obtain ⟨f, hf0, hker⟩ := Submodule.exists_le_ker_of_lt_top _ hlt
  set c : Fin N → L := fun i => f (fun j => if i = j then 1 else 0) with hcdef
  have hfc : ∀ x : Fin N → L, f x = ∑ i, x i * c i := by
    intro x
    rw [LinearMap.pi_apply_eq_sum_univ]
    rfl
  have hc0 : ∃ i, c i ≠ 0 := by
    by_contra hc
    push_neg at hc
    apply hf0
    refine LinearMap.ext fun x => ?_
    rw [hfc]
    simp [hc]
  obtain ⟨i0, hi0⟩ := hc0
  let u : InfinitePlace L → Fin N → ℂ := fun w i => w.embedding (c i)
  let A : InfinitePlace L → Matrix (Fin N) (Fin N) ℂ := fun w => vecMulVec (star (u w)) (u w)
  have hA : ∀ w, (A w).PosSemidef := fun w => posSemidef_vecMulVec_star_self (u w)
  let k : HS L N := mkHS A (fun w => (hA w).isHermitian)
  have hmat : ∀ w, mat k w = A w := fun w => rfl
  have hkP : k ∈ Psd L N := by
    intro w
    rw [hmat]
    exact hA w
  have hq : ∀ y ∈ M, q k y = 0 := by
    intro y hy
    have hyk : f (toL y) = 0 := hker (Submodule.subset_span ⟨y, hy, rfl⟩)
    rw [hfc] at hyk
    show ∑ w, (star (toR y w) ⬝ᵥ mat k w *ᵥ toR y w).re = 0
    refine Finset.sum_eq_zero fun w _ => ?_
    have hsum : ∑ j, u w j * toR y w j = 0 := by
      have : w.embedding (∑ j, toL y j * c j) = 0 := by rw [hyk, map_zero]
      rw [map_sum] at this
      rw [← this]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_mul, mul_comm]
      rfl
    have hAz : mat k w *ᵥ toR y w = 0 := by
      funext i
      rw [hmat]
      simp only [A, mulVec, dotProduct, vecMulVec_apply, mul_assoc, ← Finset.mul_sum, hsum,
        mul_zero, Pi.zero_apply]
    rw [hAz]
    simp
  have hk0 := hM k hkP hq
  have w0 : InfinitePlace L := Classical.arbitrary _
  have h1 : mat k w0 i0 i0 = 0 := by
    rw [hk0]
    rfl
  rw [hmat] at h1
  simp only [A, vecMulVec_apply, Pi.star_apply, u] at h1
  have hne : w0.embedding (c i0) ≠ 0 := (map_ne_zero _).mpr hi0
  exact hne (by
    rcases mul_eq_zero.mp h1 with h | h
    · exact star_eq_zero.mp h
    · exact h)
