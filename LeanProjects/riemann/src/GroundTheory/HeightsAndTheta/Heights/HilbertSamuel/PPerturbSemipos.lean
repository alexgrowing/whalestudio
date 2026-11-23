import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsPerturbSemipos
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PFsLineSmooth
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PFsLineLevi
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter Topology

noncomputable section

set_option linter.unusedSectionVars false

namespace PerturbedSemipositivity

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem blocks_mem_nhds {z : (Σ k, ι k) → ℂ} (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) :
    {y : (Σ k, ι k) → ℂ | ∀ k, ∃ i, y ⟨k, i⟩ ≠ 0} ∈ 𝓝 z := by
  have hopen : ∀ k, ∀ᶠ y in 𝓝 z, ∃ i, y ⟨k, i⟩ ≠ 0 := fun k => by
    obtain ⟨i, hi⟩ := hz k
    exact Filter.mem_of_superset (((continuous_apply _).isOpen_preimage _ isOpen_ne).mem_nhds hi)
      fun y hy => ⟨i, hy⟩
  exact Filter.eventually_all.mpr hopen

theorem contDiffAt_log_h (A : HermLine ι) (hA : IsSmoothHerm A) {z : (Σ k, ι k) → ℂ}
    (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) : ContDiffAt ℝ 2 (fun y => Real.log (A.h y)) z := by
  have h := hA.contDiffAt (blocks_mem_nhds hz)
  exact (h.of_le (show ((2 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) from WithTop.coe_le_coe.mpr le_top)).log (A.pos z hz).ne'

theorem levi_const_mul {f : ((Σ k, ι k) → ℂ) → ℝ} {z : (Σ k, ι k) → ℂ} (c : ℝ) (hf : ContDiffAt ℝ 2 f z)
    (w : (Σ k, ι k) → ℂ) :
    ReciprocityTheory.AnForm.levi (fun y => c * f y) z w = c * ReciprocityTheory.AnForm.levi f z w := by
  have h := ReciprocityTheory.AnForm.levi_add_smul (f := fun _ => (0 : ℝ)) (g := f) c contDiffAt_const hf w
  have h0 : ReciprocityTheory.AnForm.levi (fun _ : (Σ k, ι k) → ℂ => (0 : ℝ)) z w = 0 := by
    simp [ReciprocityTheory.AnForm.levi]
  simp only [zero_add] at h
  rw [h, h0, zero_add]

end PerturbedSemipositivity

open PerturbedSemipositivity in

theorem PerturbSemipos.proof : PerturbSemipos.Statement := by
  intro K _ ι _ P0 P M b a hM hb ha
  obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hb
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le ha
  have hH : IsSmoothHerm (fsH ι) := FsLineSmooth.proof K ι
  have hfun : (HermLine.zcomb M (fsH ι) m n).h = fun y => M.h y ^ m * (fsH ι).h y ^ n := by
    funext y
    simp [HermLine.zcomb]
  refine ⟨?_, fun z hz w hw => ?_⟩
  · have hMs : IsSmoothHerm M := hM.1
    unfold IsSmoothHerm at hMs hH ⊢
    rw [hfun]
    exact (hMs.pow m).mul (hH.pow n)
  · have hz' := hz.1
    have hev : (fun y => Real.log ((HermLine.zcomb M (fsH ι) m n).h y)) =ᶠ[𝓝 z]
        fun y => (m : ℝ) * Real.log (M.h y) + (n : ℝ) * Real.log ((fsH ι).h y) := by
      filter_upwards [blocks_mem_nhds hz'] with y hy
      rw [hfun, Real.log_mul (pow_ne_zero _ (M.pos y hy).ne') (pow_ne_zero _ ((fsH ι).pos y hy).ne'),
        Real.log_pow, Real.log_pow]
    have hfM := contDiffAt_log_h M hM.1 hz'
    have hfH := contDiffAt_log_h (fsH ι) hH hz'
    have hadd := ReciprocityTheory.AnForm.levi_add_smul (f := fun y => (m : ℝ) * Real.log (M.h y))
      (g := fun y => Real.log ((fsH ι).h y)) (n : ℝ) (contDiffAt_const.mul hfM) hfH w
    beta_reduce at hadd
    have h1 : 0 ≤ leviForm (fun y => Real.log (M.h y)) z w := hM.2 z hz w hw
    have h2 : 0 ≤ leviForm (fun y => Real.log ((fsH ι).h y)) z w := FsLineLevi.proof K ι z w hz'
    change 0 ≤ ReciprocityTheory.AnForm.levi _ z w
    rw [ReciprocityTheory.AnForm.levi_congr hev, hadd, levi_const_mul (m : ℝ) hfM w]
    exact add_nonneg (mul_nonneg (Nat.cast_nonneg m) h1) (mul_nonneg (Nat.cast_nonneg n) h2)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
