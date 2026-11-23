import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsAlgebraMapEqRoot
open PowerSeries GlobalTheory.BK

namespace GlobalTheory.CoeffComplete

open Filter Topology

variable {l : ℕ} [Fact l.Prime] {O K : Type} [CommRing O] [Algebra ℤ_[l] O]
  [NormedField K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K]

theorem norm_natCast_prime_eq : ‖(l : K)‖ = (l : ℝ)⁻¹ := by
  rw [← map_natCast (algebraMap ℚ_[l] K) l, norm_algebraMap']
  exact Padic.norm_p

theorem natCast_smul_pow_eq (k : ℕ) (z : O) : ((l : ℤ_[l]) ^ k) • z = (l : O) ^ k * z := by
  rw [Algebra.smul_def, map_pow, map_natCast]

theorem norm_intCoord_le_one {ι : Type} [Fintype ι] (v : ι → ℤ_[l]) : ‖v‖ ≤ 1 :=
  (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => PadicInt.norm_le_one _

variable {ι : Type} [Fintype ι] (b : Module.Basis ι ℤ_[l] O)

theorem coord_small_of_small (y : O) (k : ℕ) (h : ‖algebraMap O K y‖ ≤ ‖(l : K)‖ ^ k) :
    ‖b.equivFun y‖ ≤ ‖(l : ℤ_[l])‖ ^ k := by
  have hl : (l : K) ≠ 0 := by
    rw [← norm_ne_zero_iff, norm_natCast_prime_eq (l := l)]
    exact inv_ne_zero (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)
  have hw : ‖algebraMap O K y / (l : K) ^ k‖ ≤ 1 := by
    rw [norm_div, norm_pow]
    exact div_le_one_of_le₀ h (by positivity)
  obtain ⟨z, hz⟩ := (IsUnitBall.mem_range_iff (O := O) _).2 hw
  have hy : y = (l : O) ^ k * z := by
    apply IsUnitBall.inj (K := K)
    rw [map_mul, hz, map_pow, map_natCast, mul_div_cancel₀ _ (pow_ne_zero _ hl)]
  rw [hy, ← natCast_smul_pow_eq, map_smul]
  calc ‖((l : ℤ_[l]) ^ k) • b.equivFun z‖ ≤ ‖(l : ℤ_[l]) ^ k‖ * ‖b.equivFun z‖ := norm_smul_le _ _
    _ ≤ ‖(l : ℤ_[l]) ^ k‖ * 1 := by gcongr; exact norm_intCoord_le_one _
    _ = ‖(l : ℤ_[l])‖ ^ k := by rw [mul_one, norm_pow]

theorem small_of_coord_small (y : O) (k : ℕ) (h : ‖b.equivFun y‖ ≤ ‖(l : ℤ_[l])‖ ^ k) :
    ‖algebraMap O K y‖ ≤ ‖(l : K)‖ ^ k := by
  have hd : ∀ i, ((l : ℤ_[l]) ^ k) ∣ b.equivFun y i := by
    intro i
    rw [← Ideal.mem_span_singleton, ← PadicInt.norm_le_pow_iff_mem_span_pow]
    have := (pi_norm_le_iff_of_nonneg (by positivity)).1 h i
    rw [PadicInt.norm_p, inv_pow, ← zpow_natCast, ← zpow_neg] at this
    exact this
  choose e he using hd
  have hy : y = (l : O) ^ k * b.equivFun.symm e := by
    rw [← natCast_smul_pow_eq, ← map_smul, ← b.equivFun.symm_apply_apply y]
    congr 1
    funext i
    simp [he i]
  rw [hy, map_mul, map_pow, map_natCast, norm_mul, norm_pow]
  exact mul_le_of_le_one_right (by positivity) (norm_algebraMap_le _)

theorem completeSpace_of_finite_unitBall : ∀ (l : ℕ) [Fact l.Prime] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K], CompleteSpace K := by
  intro l _ O K _ _ _ _ _ _ _ _ _
  let b := Module.Free.chooseBasis ℤ_[l] O
  have hl1 : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hϖ0 : 0 < ‖(l : K)‖ := by rw [norm_natCast_prime_eq (l := l)]; positivity
  have hϖ1 : ‖(l : K)‖ < 1 := by
    rw [norm_natCast_prime_eq (l := l)]; exact inv_lt_one_of_one_lt₀ hl1
  have hπ0 : 0 < ‖(l : ℤ_[l])‖ := by rw [PadicInt.norm_p]; positivity
  have hπ1 : ‖(l : ℤ_[l])‖ < 1 := by rw [PadicInt.norm_p]; exact inv_lt_one_of_one_lt₀ hl1
  refine Metric.complete_of_convergent_controlled_sequences (fun N => ‖(l : K)‖ ^ N)
    (fun n => pow_pos hϖ0 n) ?_
  intro u hu
  have h0 : ∀ n, ‖u n - u 0‖ ≤ 1 := fun n => by
    have := hu 0 n 0 (Nat.zero_le _) le_rfl
    rw [dist_eq_norm, pow_zero] at this
    exact this.le
  choose y hy using fun n => (IsUnitBall.mem_range_iff (O := O) _).2 (h0 n)
  have hc : CauchySeq (fun n => b.equivFun (y n)) := by
    refine cauchySeq_of_le_tendsto_0 (fun N => ‖(l : ℤ_[l])‖ ^ N) (fun n m N hn hm => ?_) ?_
    · rw [dist_eq_norm, ← map_sub]
      apply coord_small_of_small (K := K) b
      rw [map_sub, hy, hy, show u n - u 0 - (u m - u 0) = u n - u m by abel]
      have := hu N n m hn hm
      rw [dist_eq_norm] at this
      exact this.le
    · exact tendsto_pow_atTop_nhds_zero_of_lt_one hπ0.le hπ1
  obtain ⟨γ, hγ⟩ := cauchySeq_tendsto_of_complete hc
  refine ⟨u 0 + algebraMap O K (b.equivFun.symm γ), ?_⟩
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hε hϖ1
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hγ _ (pow_pos hπ0 k)
  refine ⟨N, fun n hn => ?_⟩
  rw [dist_eq_norm]
  have e : u n - (u 0 + algebraMap O K (b.equivFun.symm γ)) =
      algebraMap O K (y n - b.equivFun.symm γ) := by
    rw [map_sub, hy]; abel
  rw [e]
  refine lt_of_le_of_lt (small_of_coord_small b _ k ?_) hk
  rw [map_sub, LinearEquiv.apply_symm_apply]
  have := hN n hn
  rw [dist_eq_norm] at this
  exact this.le

end GlobalTheory.CoeffComplete
