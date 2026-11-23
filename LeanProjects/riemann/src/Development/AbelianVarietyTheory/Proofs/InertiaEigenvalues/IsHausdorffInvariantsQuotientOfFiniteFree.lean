import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ImagePolynomialAction

namespace GlobalTheory.InertiaEigenvalues.FreeHausdorff

open PowerSeries GlobalTheory.BK

theorem eq_zero_of_mem_pow {O K : Type} [CommRing O] [NormedField K] [Algebra O K]
    [IsUnitBall O K] {l : ℕ} (hl : ‖(l : K)‖ < 1) {y : O}
    (hy : ∀ n : ℕ, y ∈ Ideal.span {(l : O)} ^ n) : y = 0 := by
  have hb : ∀ n : ℕ, ‖algebraMap O K y‖ ≤ ‖(l : K)‖ ^ n := by
    intro n
    have h := hy n
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at h
    obtain ⟨a, rfl⟩ := h
    have ha : ‖algebraMap O K a‖ ≤ 1 :=
      (IsUnitBall.mem_range_iff (O := O) (algebraMap O K a)).1 ⟨a, rfl⟩
    rw [map_mul, map_pow, map_natCast, norm_mul, norm_pow]
    calc ‖algebraMap O K a‖ * ‖(l : K)‖ ^ n ≤ 1 * ‖(l : K)‖ ^ n :=
          mul_le_mul_of_nonneg_right ha (pow_nonneg (norm_nonneg _) n)
      _ = ‖(l : K)‖ ^ n := one_mul _
  have h0 : ‖algebraMap O K y‖ ≤ 0 :=
    ge_of_tendsto' (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) hl) hb
  have h1 : algebraMap O K y = 0 := norm_le_zero_iff.1 h0
  exact IsUnitBall.inj (K := K) (h1.trans (map_zero _).symm)

theorem isHausdorff_ring {O K : Type} [CommRing O] [NormedField K] [Algebra O K]
    [IsUnitBall O K] {l : ℕ} (hl : ‖(l : K)‖ < 1) : IsHausdorff (Ideal.span {(l : O)}) O := by
  refine ⟨fun x hx => eq_zero_of_mem_pow (K := K) hl fun n => ?_⟩
  have h := SModEq.sub_mem.1 (hx n)
  simpa [smul_eq_mul, Ideal.mul_top] using h

theorem isHausdorff_of_free {R M : Type} [CommRing R] [AddCommGroup M] [Module R M]
    [Module.Free R M] (I : Ideal R) [h : IsHausdorff I R] : IsHausdorff I M := by
  refine ⟨fun x hx => ?_⟩
  let b := Module.Free.chooseBasis R M
  refine b.ext_elem fun i => ?_
  rw [map_zero, Finsupp.zero_apply]
  refine h.haus _ fun n => ?_
  have hxn : x ∈ I ^ n • (⊤ : Submodule R M) := by simpa using SModEq.sub_mem.1 (hx n)
  have hle : (I ^ n • (⊤ : Submodule R M)).map (b.coord i) ≤ I ^ n • (⊤ : Submodule R R) := by
    rw [Submodule.map_le_iff_le_comap]
    refine Submodule.smul_le.2 fun r hr m _ => ?_
    rw [Submodule.mem_comap, map_smul]
    exact Submodule.smul_mem_smul hr Submodule.mem_top
  have := hle (Submodule.mem_map_of_mem hxn)
  rw [SModEq.sub_mem, sub_zero]
  simpa using this

end GlobalTheory.InertiaEigenvalues.FreeHausdorff

namespace GlobalTheory.InertiaEigenvalues

open PowerSeries GlobalTheory.BK

theorem isHausdorff_Z_of_finiteFree : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (η H : ℕ) (D : BKDat O K l e a ι η H), GlobalTheory.IndefiniteRowSideFullHecke.ImagePolynomialAction.FiniteFree D → IsHausdorff (Ideal.span {(l : O)}) D.Z := by
  intro O K _ _ _ _ _ _ l e a ι _ _ _ _ _ _ _ η H D hD
  haveI : Module.Free O D.Z := hD.1
  haveI : IsHausdorff (Ideal.span {(l : O)}) O :=
    FreeHausdorff.isHausdorff_ring (K := K) (norm_l_lt_one (K := K) l)
  exact FreeHausdorff.isHausdorff_of_free _

end GlobalTheory.InertiaEigenvalues
