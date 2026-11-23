import Mathlib

namespace CrystallineSemistableComparison.Onto

open scoped BigOperators

theorem onto_la {k0 L V J : Type*} [Field k0] [Field L] [AddCommGroup V] [Module k0 V]
    [FiniteDimensional k0 V] (F : J → V → L)
    (hInj : ∀ {k : ℕ} (b : Module.Basis (Fin k) k0 V) (z : Fin k → L),
      (∀ j, ∑ i, z i * F j (b i) = 0) → z = 0)
    {m : ℕ} (u : Fin m → V) (hu : LinearIndependent k0 u) (t : Fin m → L) :
    ∃ (S : Finset J) (c : J → L), ∀ s, ∑ j ∈ S, c j * F j (u s) = t s := by
  classical
  have hs : LinearIndepOn k0 id (Set.range u) := (linearIndepOn_id_range_iff hu.injective).2 hu
  let B := Module.Basis.extend hs
  have : Finite (hs.extend (Set.subset_univ _)) := Module.Finite.finite_basis B
  obtain ⟨k, ⟨eqv⟩⟩ := Finite.exists_equiv_fin (hs.extend (Set.subset_univ _))
  let b : Module.Basis (Fin k) k0 V := B.reindex eqv
  let e : Fin m → Fin k := fun s => eqv ⟨u s, hs.subset_extend _ ⟨s, rfl⟩⟩
  have hbe : ∀ s, b (e s) = u s := by
    intro s
    simp [b, e, B, Module.Basis.reindex_apply, Module.Basis.extend_apply_self]
  have he : Function.Injective e := by
    intro s s' h
    apply hu.injective
    rw [← hbe s, ← hbe s', h]
  let vec : J → Fin k → L := fun j i => F j (b i)
  have hW : Submodule.span L (Set.range vec) = ⊤ := by
    by_contra hne
    obtain ⟨f, hf0, hle⟩ := (Submodule.span L (Set.range vec)).exists_le_ker_of_lt_top
      (lt_top_iff_ne_top.2 hne)
    let z : Fin k → L := fun i => f (fun j => if i = j then 1 else 0)
    have hz : z = 0 := by
      apply hInj b z
      intro j
      have h1 : f (vec j) = 0 := hle (Submodule.subset_span ⟨j, rfl⟩)
      rw [LinearMap.pi_apply_eq_sum_univ f (vec j)] at h1
      rw [← h1]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      simp [z, vec, smul_eq_mul, mul_comm]
    apply hf0
    refine LinearMap.ext fun x => ?_
    rw [LinearMap.pi_apply_eq_sum_univ f x]
    have : ∀ i, f (fun j => if i = j then (1 : L) else 0) = 0 := fun i => congrFun hz i
    simp [this]
  have hT : Function.extend e t 0 ∈ Submodule.span L (Set.range vec) := by
    rw [hW]; exact Submodule.mem_top
  obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 hT
  refine ⟨c.support, c, fun s => ?_⟩
  have h2 := congrFun hc (e s)
  rw [he.extend_apply] at h2
  rw [← h2, Finsupp.sum, Finset.sum_apply]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  simp [vec, hbe s]

end CrystallineSemistableComparison.Onto
