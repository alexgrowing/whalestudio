import Mathlib
import ReciprocityTheory.L2DbarEstimates.Imports
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourSignHolds
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
import Development.AbelianVarietyTheory.Definitions.Divisors.EtaleEmpty
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.AApproxE
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHoloQuadraticAddLeviIsLittleOStatement
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory

theorem leviV_re_le_sum_norm {n : ℕ} (g : V n → ℂ) (p ζ : V n) :
    (leviV n g p ζ.ofLp).re ≤
      (∑ j, ∑ k, ‖wd n j (wdb n k g) p‖) * ‖ζ‖ ^ 2 := by
  calc (leviV n g p ζ.ofLp).re ≤ ‖leviV n g p ζ.ofLp‖ := Complex.re_le_norm _
    _ ≤ ∑ j, ‖∑ k, wd n j (wdb n k g) p * ζ.ofLp j * (starRingEnd ℂ) (ζ.ofLp k)‖ :=
        norm_sum_le _ _
    _ ≤ ∑ j, ∑ k, ‖wd n j (wdb n k g) p‖ * ‖ζ‖ ^ 2 := by
        gcongr with j _
        refine (norm_sum_le _ _).trans ?_
        gcongr with k _
        rw [norm_mul, norm_mul, Complex.norm_conj, sq, ← mul_assoc]
        have hj : ‖ζ.ofLp j‖ ≤ ‖ζ‖ := PiLp.norm_apply_le ζ j
        have hk : ‖ζ.ofLp k‖ ≤ ‖ζ‖ := PiLp.norm_apply_le ζ k
        gcongr
    _ = (∑ j, ∑ k, ‖wd n j (wdb n k g) p‖) * ‖ζ‖ ^ 2 := by
        simp only [Finset.sum_mul]

theorem psh_normal_frame : ∀ (n : ℕ) (O : Set (V n)) (φ : V n → ℝ) (p : V n), IsOpen O → p ∈ O → ContDiffOn ℝ ∞ φ O → (∀ ξ : Fin n → ℂ, ξ ≠ 0 → 0 < (leviV n (fun w => ((φ w : ℝ) : ℂ)) p ξ).re) → ∃ (q : V n → ℂ) (c C ρ : ℝ), Differentiable ℂ q ∧ 0 < c ∧ 0 < C ∧ 0 < ρ ∧ closedBall p ρ ⊆ O ∧ ∀ v ∈ closedBall p ρ, c * ‖v - p‖ ^ 2 ≤ φ v - 2 * (q v).re ∧ φ v - 2 * (q v).re ≤ C * ‖v - p‖ ^ 2 := by
  intro n O φ p hO hp hφ hlevi
  set g : V n → ℂ := fun w => ((φ w : ℝ) : ℂ) with hg
  have hgs : ContDiffOn ℝ ∞ g O := Complex.ofRealCLM.contDiff.comp_contDiffOn hφ
  obtain ⟨m, hm, hmb⟩ := levi_pos_compact (g := g) hO hgs (K0 := {p}) isCompact_singleton
    (Set.singleton_subset_iff.2 hp) (fun u hu ζ hζ => by
      rw [Set.mem_singleton_iff.1 hu]
      refine hlevi _ ?_
      intro h0; apply hζ
      exact (WithLp.ofLp_eq_zero 2).1 h0)
  have hφ2 : ContDiffAt ℝ 2 φ p :=
    ((hφ.contDiffAt (hO.mem_nhds hp)).of_le (by norm_cast))
  obtain ⟨q, hq, ho⟩ := GlobalTheory.T.exists_holo_quadratic_add_levi_isLittleO n φ p hφ2
  set A : ℝ := ∑ j, ∑ k, ‖wd n j (wdb n k g) p‖ with hA
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun k _ => norm_nonneg _
  have hev := ho.def (half_pos hm)
  obtain ⟨ε, hε, hεb⟩ := Metric.eventually_nhds_iff.1 hev
  obtain ⟨ε2, hε2, hε2O⟩ := Metric.isOpen_iff.1 hO p hp
  refine ⟨q, m / 2, A + m / 2, min ε ε2 / 2, hq, half_pos hm, by positivity,
    by positivity, ?_, ?_⟩
  · intro v hv
    apply hε2O
    rw [mem_closedBall] at hv
    rw [mem_ball]
    have : min ε ε2 / 2 < ε2 := by
      have := min_le_right ε ε2; linarith [lt_min hε hε2]
    linarith
  · intro v hv
    rw [mem_closedBall] at hv
    have hvε : dist v p < ε := by
      have := min_le_left ε ε2; linarith [lt_min hε hε2]
    have hR := hεb hvε
    rw [Real.norm_eq_abs, norm_pow, norm_norm] at hR
    have hlo := hmb p rfl (v - p)
    have hup := leviV_re_le_sum_norm g p (v - p)
    have habs := abs_le.1 hR
    change m * ‖v - p‖ ^ 2 ≤ (leviV n g p (fun j => (v - p) j)).re at hlo
    change (leviV n g p (fun j => (v - p) j)).re ≤ A * ‖v - p‖ ^ 2 at hup
    constructor <;> nlinarith [habs.1, habs.2, sq_nonneg ‖v - p‖]

end GlobalTheory
