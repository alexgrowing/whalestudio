import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.PowerSeriesOneAddConstMulXMulInv

noncomputable section
namespace GlobalTheory.LatticeComap
open GlobalTheory.PhiGam

section
variable {k : Type} [Field k] {V : Type} [AddCommGroup V] [Module (LaurentSeries k) V]
  [Module (PowerSeries k) V] [IsScalarTower (PowerSeries k) (LaurentSeries k) V]

theorem exists_pow_smul_mem {N : Submodule (PowerSeries k) V}
    (hN : Submodule.span (LaurentSeries k) (N : Set V) = ⊤) (x : V) :
    ∃ m : ℕ, ((PowerSeries.X : PowerSeries k) ^ m) • x ∈ N := by
  have hx : x ∈ Submodule.span (LaurentSeries k) (N : Set V) := by rw [hN]; trivial
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨0, by simpa using hy⟩
  | zero => exact ⟨0, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨m1, h1⟩ := hy
    obtain ⟨m2, h2⟩ := hz
    refine ⟨m1 + m2, ?_⟩
    rw [smul_add]
    refine N.add_mem ?_ ?_
    · rw [pow_add, mul_comm, mul_smul]; exact N.smul_mem _ h1
    · rw [pow_add, mul_smul]; exact N.smul_mem _ h2
  | smul a y _ hy =>
    obtain ⟨m, hm⟩ := hy
    obtain ⟨⟨p, s⟩, hps⟩ := IsLocalization.surj (Submonoid.powers (PowerSeries.X : PowerSeries k)) a
    obtain ⟨j, hj⟩ := s.2
    have hj' : (PowerSeries.X : PowerSeries k) ^ j = (s : PowerSeries k) := hj
    have hps' : a * algebraMap (PowerSeries k) (LaurentSeries k) (s : PowerSeries k) =
        algebraMap (PowerSeries k) (LaurentSeries k) p := hps
    have key : ((PowerSeries.X : PowerSeries k) ^ j) • a • y = p • y := by
      rw [← algebraMap_smul (LaurentSeries k) ((PowerSeries.X : PowerSeries k) ^ j) (a • y), smul_smul, hj',
        mul_comm, hps', algebraMap_smul]
    refine ⟨m + j, ?_⟩
    rw [pow_add, mul_smul, key, smul_comm]
    exact N.smul_mem _ hm

variable {W : Type} [AddCommGroup W] [Module (LaurentSeries k) W]
  [Module (PowerSeries k) W] [IsScalarTower (PowerSeries k) (LaurentSeries k) W]

theorem isLat_comap (f : W →ₗ[LaurentSeries k] V) (hf : Function.Injective f)
    {N : Submodule (PowerSeries k) V} (hN : IsLat N) :
    IsLat (N.comap (f.restrictScalars (PowerSeries k))) := by
  refine ⟨?_, ?_⟩
  · refine Submodule.fg_of_fg_map_injective (f.restrictScalars (PowerSeries k)) hf ?_
    haveI : IsNoetherian (PowerSeries k) N := isNoetherian_of_fg_of_noetherian N hN.1
    exact isNoetherian_submodule.1 this _ (Submodule.map_comap_le _ _)
  · refine eq_top_iff.2 fun w _ => ?_
    obtain ⟨m, hm⟩ := exists_pow_smul_mem hN.2 (f w)
    have hmem : ((PowerSeries.X : PowerSeries k) ^ m) • w ∈ N.comap (f.restrictScalars (PowerSeries k)) := by
      rw [Submodule.mem_comap, LinearMap.restrictScalars_apply, LinearMap.map_smul_of_tower]
      exact hm
    have hne : algebraMap (PowerSeries k) (LaurentSeries k) ((PowerSeries.X : PowerSeries k) ^ m) ≠ 0 := by
      rw [map_pow]
      refine pow_ne_zero _ ?_
      intro h
      have hX : (PowerSeries.X : PowerSeries k) ≠ 0 := PowerSeries.X_ne_zero
      exact hX (HahnSeries.ofPowerSeries_injective (Γ := ℤ) (R := k) (by rw [map_zero]; exact h))
    rw [← Submodule.smul_mem_iff _ hne, algebraMap_smul]
    exact Submodule.subset_span hmem

end

theorem main : ∀ {k : Type} [inst : Field k] {V : Type} [inst_1 : AddCommGroup V]
    [inst_2 : Module (LaurentSeries k) V] [inst_3 : Module (PowerSeries k) V]
    [inst_4 : IsScalarTower (PowerSeries k) (LaurentSeries k) V] {W : Type} [inst_5 : AddCommGroup W]
    [inst_6 : Module (LaurentSeries k) W] [inst_7 : Module (PowerSeries k) W]
    [inst_8 : IsScalarTower (PowerSeries k) (LaurentSeries k) W] (f : LinearMap (RingHom.id (LaurentSeries k)) W V),
    Function.Injective (DFunLike.coe f) → ∀ {N : Submodule (PowerSeries k) V}, GlobalTheory.PhiGam.IsLat N →
      GlobalTheory.PhiGam.IsLat (Submodule.comap (LinearMap.restrictScalars (PowerSeries k) f) N) :=
  fun f hf _ hN => isLat_comap f hf hN

end GlobalTheory.LatticeComap
