import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelKlingenDeligneRibet
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.AbelContinuation
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.CongSubgroup

open NumberField NumberField.Units NumberField.Units.dirichletUnitTheorem GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Cones

namespace GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.UnitLattice

theorem multiples_relativelyDense (F : Type) [Field F] [NumberField F] (e : ℕ) (he : 0 < e) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : logSpace F, ∃ u : (𝓞 F)ˣ,
      ∀ w, |y w + (e : ℝ) * logEmbedding F (Additive.ofMul u) w| ≤ C := by
  classical
  let b := (basisUnitLattice F).ofZLatticeBasis ℝ (unitLattice F)
  let R : ℝ := ∑ i, ‖b i‖
  have hR0 : 0 ≤ R := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have he0 : (0 : ℝ) < e := by exact_mod_cast he
  refine ⟨(e : ℝ) * R, by positivity, fun y => ?_⟩
  let v : logSpace F := fun w => -(y w) / (e : ℝ)
  have hfl : ((ZSpan.floor b v : _) : logSpace F) ∈ unitLattice F := by
    rw [← (basisUnitLattice F).ofZLatticeBasis_span ℝ (unitLattice F)]
    exact (ZSpan.floor b v).2
  obtain ⟨x, -, hx⟩ := Submodule.mem_map.mp hfl
  refine ⟨Additive.toMul x, fun w => ?_⟩
  have hfr : ‖v - (ZSpan.floor b v : logSpace F)‖ ≤ R := by
    simpa [ZSpan.fract_apply] using ZSpan.norm_fract_le b v
  have h1 := norm_le_pi_norm (v - (ZSpan.floor b v : logSpace F)) w
  rw [← hx] at h1 hfr
  have h2 : (logEmbedding F).toIntLinearMap x w
      = logEmbedding F (Additive.ofMul (Additive.toMul x)) w := rfl
  rw [Pi.sub_apply, h2, Real.norm_eq_abs] at h1
  have h3 : y w + (e : ℝ) * logEmbedding F (Additive.ofMul (Additive.toMul x)) w
      = -((e : ℝ) * (v w - logEmbedding F (Additive.ofMul (Additive.toMul x)) w)) := by
    simp only [v]; field_simp; ring
  rw [h3, abs_neg, abs_mul, abs_of_pos he0]
  exact mul_le_mul_of_nonneg_left (h1.trans hfr) he0.le

end GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.UnitLattice
