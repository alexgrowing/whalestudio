import Mathlib

namespace GlobalTheory.SpanOfResidue

theorem mem_smul_top_of_entries {A : Type} [CommRing A] {r : ℕ} (I : Ideal A)
    (d : Matrix (Fin r) (Fin r) A) (hd : ∀ i j, d i j ∈ I) :
    d ∈ I • (⊤ : Submodule A (Matrix (Fin r) (Fin r) A)) := by
  rw [Matrix.matrix_eq_sum_single d]
  refine Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun j _ => ?_
  have h : Matrix.single i j (d i j) = d i j • Matrix.single i j (1 : A) := by
    rw [Matrix.smul_single, smul_eq_mul, mul_one]
  rw [h]
  exact Submodule.smul_mem_smul (hd i j) Submodule.mem_top

theorem span_eq_top_of_residue {ι A : Type} [CommRing A] [IsLocalRing A] {r : ℕ}
    (f : ι → Matrix (Fin r) (Fin r) A)
    (h : Submodule.span (IsLocalRing.ResidueField A)
      (Set.range fun (i : ι) ↦ Matrix.map (f i)
        (⇑(IsLocalRing.residue A) : A → IsLocalRing.ResidueField A)) = ⊤) :
    Submodule.span A (Set.range f) = ⊤ := by
  have key : ∀ y ∈ Submodule.span (IsLocalRing.ResidueField A)
      (Set.range fun (i : ι) ↦ Matrix.map (f i)
        (⇑(IsLocalRing.residue A) : A → IsLocalRing.ResidueField A)),
      ∃ n ∈ Submodule.span A (Set.range f),
        Matrix.map n (⇑(IsLocalRing.residue A) : A → IsLocalRing.ResidueField A) = y := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      exact ⟨f i, Submodule.subset_span ⟨i, rfl⟩, rfl⟩
    | zero =>
      refine ⟨0, Submodule.zero_mem _, ?_⟩
      ext i j
      simp
    | add x y _ _ hx hy =>
      obtain ⟨n, hn, rfl⟩ := hx
      obtain ⟨m, hm, rfl⟩ := hy
      refine ⟨n + m, Submodule.add_mem _ hn hm, ?_⟩
      ext i j
      simp
    | smul c x _ hx =>
      obtain ⟨n, hn, rfl⟩ := hx
      obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective c
      refine ⟨a • n, Submodule.smul_mem _ a hn, ?_⟩
      ext i j
      simp
  rw [eq_top_iff]
  refine Submodule.le_of_le_smul_of_le_jacobson_bot (I := IsLocalRing.maximalIdeal A)
    Module.Finite.fg_top (IsLocalRing.maximalIdeal_le_jacobson _) ?_
  intro x _
  obtain ⟨n, hn, hnx⟩ := key (Matrix.map x (IsLocalRing.residue A)) (h ▸ Submodule.mem_top)
  have hx : x = n + (x - n) := by abel
  rw [hx]
  refine Submodule.add_mem_sup hn (mem_smul_top_of_entries _ _ fun i j => ?_)
  rw [← IsLocalRing.residue_eq_zero_iff, Matrix.sub_apply, map_sub, sub_eq_zero]
  exact (congrFun (congrFun hnx i) j).symm

end GlobalTheory.SpanOfResidue
