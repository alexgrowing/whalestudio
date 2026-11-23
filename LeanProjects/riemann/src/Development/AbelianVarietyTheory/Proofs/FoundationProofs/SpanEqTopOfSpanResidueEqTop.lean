import Mathlib

namespace GlobalTheory.ResidueSpanLift

open IsLocalRing

theorem mem_smul_top_of_entries {O : Type} [CommRing O] {a : ℕ} (I : Ideal O)
    (X : Matrix (Fin a) (Fin a) O) (h : ∀ i j, X i j ∈ I) :
    X ∈ I • (⊤ : Submodule O (Matrix (Fin a) (Fin a) O)) := by
  rw [Matrix.matrix_eq_sum_single X]
  refine Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun j _ => ?_
  have : Matrix.single i j (X i j) = X i j • Matrix.single i j (1 : O) := by
    rw [Matrix.smul_single, smul_eq_mul, mul_one]
  rw [this]
  exact Submodule.smul_mem_smul (h i j) Submodule.mem_top

theorem exists_lift {O ι : Type} [CommRing O] [IsLocalRing O] {a : ℕ}
    (M : ι → Matrix (Fin a) (Fin a) O) (Y : Matrix (Fin a) (Fin a) (ResidueField O))
    (hY : Y ∈ Submodule.span (ResidueField O)
      (Set.range fun g : ι => (M g).map (residue O))) :
    ∃ Z ∈ Submodule.span O (Set.range M), Z.map (residue O) = Y := by
  induction hY using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨g, rfl⟩ := hx
    exact ⟨M g, Submodule.subset_span ⟨g, rfl⟩, rfl⟩
  | zero => exact ⟨0, Submodule.zero_mem _, by ext i j; simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨Z, hZ, rfl⟩ := hx
    obtain ⟨W, hW, rfl⟩ := hy
    exact ⟨Z + W, Submodule.add_mem _ hZ hW, by ext i j; simp⟩
  | smul c x _ hx =>
    obtain ⟨Z, hZ, rfl⟩ := hx
    obtain ⟨d, rfl⟩ := residue_surjective c
    refine ⟨d • Z, Submodule.smul_mem _ _ hZ, ?_⟩
    ext i j
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul]

theorem span_eq_top_of_span_residue_eq_top {O ι : Type} [CommRing O] [IsLocalRing O] {a : ℕ}
    (M : ι → Matrix (Fin a) (Fin a) O)
    (h : Submodule.span (ResidueField O)
      (Set.range fun g : ι => (M g).map (residue O)) = ⊤) :
    Submodule.span O (Set.range M) = ⊤ := by
  refine top_le_iff.mp ?_
  refine Submodule.le_of_le_smul_of_le_jacobson_bot (I := maximalIdeal O)
    Module.Finite.fg_top (maximalIdeal_le_jacobson _) ?_
  intro X _
  obtain ⟨Z, hZ, hZX⟩ := exists_lift M (X.map (residue O)) (h ▸ Submodule.mem_top)
  have hX : X = Z + (X - Z) := by abel
  rw [hX]
  refine Submodule.add_mem_sup hZ (mem_smul_top_of_entries _ _ fun i j => ?_)
  have := congrFun (congrFun hZX i) j
  simp only [Matrix.map_apply] at this
  rw [← residue_eq_zero_iff, Matrix.sub_apply, map_sub, this, sub_self]

end GlobalTheory.ResidueSpanLift
