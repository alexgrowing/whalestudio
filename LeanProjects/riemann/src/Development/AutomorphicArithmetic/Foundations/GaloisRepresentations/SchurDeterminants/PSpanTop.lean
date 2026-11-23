import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SchurDeterminants.PairSplit

noncomputable section

open Finset MvPolynomial

namespace UpperTheory.Gal.Schur

private theorem span_embeddings_mul_eq_univ_of_injective {O K ι : Type} [CommRing O] [Field K] [Fintype ι] (τ : ι → O →+* K)
    (hτ : Function.Injective τ) (N : O) (hN : ∀ t, τ t N ≠ 0) :
    Submodule.span K {v : ι → K | ∃ x : O, v = fun t => τ t (N * x)} = ⊤ := by
  classical
  by_contra hne
  obtain ⟨φ, hφ, hmap⟩ := Submodule.exists_dual_map_eq_bot_of_lt_top (lt_top_iff_ne_top.2 hne) inferInstance
  have hφv : ∀ v : ι → K, φ v = ∑ t, v t * φ (Pi.single t 1) := by
    intro v
    rw [LinearMap.pi_apply_eq_sum_univ φ v]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [smul_eq_mul]
    congr 2
    ext s
    simp [Pi.single_apply, eq_comm]
  have hzero : ∀ x : O, ∑ t, (φ (Pi.single t 1) * τ t N) * τ t x = 0 := by
    intro x
    have hx : (fun t => τ t (N * x)) ∈ Submodule.span K {v : ι → K | ∃ x : O, v = fun t => τ t (N * x)} :=
      Submodule.subset_span ⟨x, rfl⟩
    have : φ (fun t => τ t (N * x)) = 0 := by
      have h2 := Submodule.mem_map_of_mem (f := φ) hx
      rw [hmap, Submodule.mem_bot] at h2
      exact h2
    rw [hφv] at this
    rw [← this]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [map_mul]
    ring
  have hli : LinearIndependent K (fun t => ((τ t : O →* K) : O → K)) := by
    refine (linearIndependent_monoidHom O K).comp (fun t => (τ t : O →* K)) ?_
    intro a b hab
    apply hτ
    ext y
    exact DFunLike.congr_fun hab y
  have hc : ∀ t, φ (Pi.single t 1) * τ t N = 0 := by
    refine Fintype.linearIndependent_iff.1 hli _ ?_
    funext x
    simpa [Finset.sum_apply] using hzero x
  apply hφ
  refine LinearMap.ext fun v => ?_
  rw [hφv, LinearMap.zero_apply]
  refine Finset.sum_eq_zero fun t _ => ?_
  rw [(mul_eq_zero.1 (hc t)).resolve_right (hN t), mul_zero]

theorem spanTop : SpanTop := by
  classical
  intro O K ι _ _ _ τ hτ N hN k
  have hA := span_embeddings_mul_eq_univ_of_injective τ hτ N hN
  let L : Fin k → (ι → K) →ₗ[K] (ι × Fin k → K) := fun j =>
    LinearMap.pi (fun p => if p.2 = j then LinearMap.proj p.1 else 0)
  have hL : ∀ j w p, L j w p = if p.2 = j then w p.1 else 0 := by
    intro j w p
    simp only [L, LinearMap.pi_apply]
    split_ifs <;> simp
  have hsub : ∀ j, Submodule.map (L j) (Submodule.span K {v : ι → K | ∃ x : O, v = fun t => τ t (N * x)}) ≤
      Submodule.span K {x | ∃ β : Fin k → O, x = pt τ fun s ↦ N * β s} := by
    intro j
    rw [Submodule.map_span]
    refine Submodule.span_mono ?_
    rintro _ ⟨v, ⟨x, rfl⟩, rfl⟩
    refine ⟨Pi.single j x, ?_⟩
    funext p
    rw [hL]
    simp only [pt, Pi.single_apply]
    split_ifs <;> simp_all
  rw [Submodule.eq_top_iff']
  intro v
  have hv : v = ∑ j, L j (fun t => v (t, j)) := by
    funext p
    simp [Finset.sum_apply, hL]
  rw [hv]
  refine Submodule.sum_mem _ fun j _ => hsub j ?_
  refine Submodule.mem_map_of_mem ?_
  rw [hA]
  exact Submodule.mem_top

end UpperTheory.Gal.Schur
