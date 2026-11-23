import Mathlib

namespace GlobalTheory.PowerScalarMembership

theorem pow_smul_mem_of_le {O V : Type} [CommRing O] [AddCommGroup V] [Module O V]
    (L : Submodule O V) (c : O) {x : V} {m n : ℕ} (hmn : m ≤ n) (h : c ^ m • x ∈ L) :
    c ^ n • x ∈ L := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hmn
  rw [pow_add, mul_comm, mul_smul]
  exact L.smul_mem _ h

theorem exists_pow_smul_mem {LL O : Type} [Field LL] [CommRing O] [Algebra O LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V] (c : O)
    (hc : ∀ a : LL, ∃ (k : ℕ) (b : O), algebraMap O LL b = algebraMap O LL c ^ k * a)
    (L : Submodule O V) (hL : Submodule.span LL (L : Set V) = ⊤) (x : V) :
    ∃ m : ℕ, c ^ m • x ∈ L := by
  have hx : x ∈ Submodule.span LL (L : Set V) := hL ▸ Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨0, by simpa using hy⟩
  | zero => exact ⟨0, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨m, hm⟩ := hy
    obtain ⟨n, hn⟩ := hz
    refine ⟨max m n, ?_⟩
    rw [smul_add]
    exact L.add_mem (pow_smul_mem_of_le L c (le_max_left _ _) hm)
      (pow_smul_mem_of_le L c (le_max_right _ _) hn)
  | smul a y _ hy =>
    obtain ⟨m, hm⟩ := hy
    obtain ⟨k, b, hb⟩ := hc a
    refine ⟨k + m, ?_⟩
    have key : c ^ (k + m) • (a • y) = b • (c ^ m • y) := by
      rw [← algebraMap_smul LL (c ^ (k + m)), smul_smul, ← algebraMap_smul LL b,
        ← algebraMap_smul LL (c ^ m), smul_smul, hb, map_pow, map_pow, pow_add]
      congr 1
      ring
    rw [key]
    exact L.smul_mem b hm

theorem main : ∀ {LL O : Type} [inst : Field LL] [inst_1 : CommRing O] [inst_2 : Algebra O LL] [TopologicalSpace LL] {V : Type} [inst_4 : AddCommGroup V] [inst_5 : Module LL V] [inst_6 : Module O V] [IsScalarTower O LL V] (c : O), (∀ (a : LL), ∃ (k : ℕ) (b : O), (Algebra.algebraMap O LL : O → LL) b = (Algebra.algebraMap O LL : O → LL) c ^ k * a) → ∀ (L S : Submodule O V), Submodule.span LL (↑L : Set V) = ⊤ → Submodule.FG S → ∃ (m : ℕ), ∀ x ∈ S, c ^ m • x ∈ L := by
  intro LL O _ _ _ _ V _ _ _ _ c hc L S hL hS
  obtain ⟨s, rfl⟩ := hS
  choose f hf using fun x => exists_pow_smul_mem (LL := LL) c hc L hL x
  refine ⟨s.sup f, fun x hx => ?_⟩
  have hle : Submodule.span O (s : Set V) ≤ L.comap ((c ^ s.sup f) • LinearMap.id) := by
    rw [Submodule.span_le]
    intro y hy
    simp only [SetLike.mem_coe, Submodule.mem_comap, LinearMap.smul_apply, LinearMap.id_apply]
    exact pow_smul_mem_of_le L c (Finset.le_sup hy) (hf y)
  simpa using hle hx

end GlobalTheory.PowerScalarMembership
