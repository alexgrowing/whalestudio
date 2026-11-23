import Mathlib
import GroundTheory.PAdicHodge.ExtRobbaDMRankOne
set_option maxSynthPendingDepth 1

noncomputable section

set_option linter.unusedSectionVars false

namespace GroundTheory.PAdicHodge

open Laurent Filter Topology UniformSpace

namespace TeichLift

variable {p : ℕ} [hp : Fact p.Prime] {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L]
  [CharP L p] [PerfectRing L p] {Γ : Type*} [CommRing Γ] (T : TeichLift p L Γ)

theorem norm_le_one_of_forall_weight_le {a : L} {n : ℕ}
    (h : ∀ ρ : ℝ, 0 < ρ → ρ < 1 → ‖a‖ * ρ ^ n ≤ 1) : ‖a‖ ≤ 1 := by
  have ht : Tendsto (fun ρ : ℝ => ‖a‖ * ρ ^ n) (𝓝[<] 1) (𝓝 (‖a‖ * 1 ^ n)) :=
    ((continuous_const.mul (continuous_pow n)).tendsto 1).mono_left nhdsWithin_le_nhds
  rw [one_pow, mul_one] at ht
  refine le_of_tendsto ht ?_
  filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with ρ hρ
  exact h ρ hρ.1 hρ.2

namespace TeichFrob

variable {T} (F : T.TeichFrob)

theorem exists_int_φ_eq_u_mul [IsAlgClosed L] (ha : 0 < F.a) :
    ∃ y ∈ T.int, ‖T.red y‖ = 1 ∧ F.φ y = F.u * y := by
  have hq := F.two_le_q ha
  have hu0 : ∀ n : ℕ, T.red F.u ^ n ≠ 0 := fun n =>
    pow_ne_zero _ (norm_ne_zero_iff.1 (by rw [F.norm_red_u]; exact one_ne_zero))
  have hw0 : T.red F.u ≠ 0 := by simpa using hu0 1
  choose r hr hr0 using fun (n : ℕ) (e : L) => exists_root_of_isAlgClosed hq (hu0 n) (T.red F.u) e
  set y := T.ofCoeff (F.approxCoeff F.u r) with hydef

  have hdig : ∀ n, ‖T.coeff y n‖ ≤ 1 := by
    intro n
    rw [hydef, T.coeff_ofCoeff]
    refine norm_le_one_of_forall_weight_le (n := n) fun ρ hρ0 hρ1 => ?_
    have hw := T.convergesAt_of_mem_int F.u_mem_int hρ0 hρ1
    have hW : gaussNorm (T.zcoeff F.u) ρ ≤ (1 : ℝ) ^ (p ^ F.a - 1) := by
      rw [T.gaussNorm_eq_one_of_mem_int F.u_mem_int F.norm_red_u hρ0 hρ1, one_pow]
    exact approxCoeff_weight_le ha hr hρ0 hρ1 hw zero_le_one hW n
  have hyint : y ∈ T.int := T.mem_int_iff.2 hdig

  have hy0 : T.red y = r 0 0 := by
    rw [← T.coeff_zero, hydef, T.coeff_ofCoeff]
    simp [approxCoeff, approx]
  have hr00 : r 0 0 ≠ 0 := hr0 0 0 rfl hw0
  have hroot := hr 0 0
  simp only [pow_zero, one_mul, add_zero] at hroot
  have hnorm : ‖r 0 0‖ = 1 := by
    have hle : ‖r 0 0‖ ≤ 1 := by rw [← hy0, ← T.coeff_zero]; exact hdig 0
    have hq1 : r 0 0 ^ (p ^ F.a - 1) = T.red F.u := by
      have : r 0 0 ^ p ^ F.a = r 0 0 ^ (p ^ F.a - 1) * r 0 0 := by
        rw [← pow_succ]; congr 1; omega
      rw [this] at hroot
      exact mul_right_cancel₀ hr00 (by linear_combination hroot)
    have h1 : ‖r 0 0‖ ^ (p ^ F.a - 1) = 1 := by rw [← norm_pow, hq1, F.norm_red_u]
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by omega)).1 h1
  refine ⟨y, hyint, by rw [hy0, hnorm], ?_⟩

  have hall : ∀ n, F.φ y - F.u * y ∈ Ideal.span {T.π ^ n} := fun n => by
    have h1 : y - F.approx F.u r n ∈ Ideal.span {T.π ^ n} := by
      rw [F.approx_eq_finSum]; exact T.mk_sub_finSum_mem _ n
    have : F.φ y - F.u * y = (F.φ (F.approx F.u r n) - F.u * F.approx F.u r n) +
        (F.φ (y - F.approx F.u r n) - F.u * (y - F.approx F.u r n)) := by
      rw [map_sub]; ring
    rw [this]
    exact add_mem (approx_mem hr n) (sub_mem (F.φ_mem_span_pow h1) (Ideal.mul_mem_left _ _ h1))
  have h0 : F.φ y - F.u * y = 0 := T.eq_of_coeff_eq (funext fun n => by
    rw [T.coeff_zero_elem]; exact T.coeff_of_mem_span (hall (n + 1)) n le_rfl)
  exact sub_eq_zero.1 h0

end TeichFrob

end TeichLift

end GroundTheory.PAdicHodge
