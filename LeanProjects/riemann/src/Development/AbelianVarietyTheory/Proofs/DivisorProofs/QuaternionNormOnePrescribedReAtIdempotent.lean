import Development.AbelianVarietyTheory.Definitions.Divisors.OneMemH0WeightZero
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import GroundTheory.GlobalFields.IdeleGroups.IdeleNorms
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.QSA GlobalTheory.Published
open Matrix
open scoped Quaternion Topology TensorProduct

namespace GlobalTheory

theorem quat_norm_one_re_at_idem : ∀ (R : Type) [CommRing R] (a b ε p q : R), ε * ε = ε → IsUnit a → IsUnit b →
    IsUnit (2 : R) → ε * (b - (p ^ 2 - a * q ^ 2)) = 0 → ∀ t : R, ∃ h : ℍ[R, a, b], nrm h = 1 ∧ ε * h.re = ε * t := by
  intro R _ a b ε p q hε ha hb h2 hE t
  obtain ⟨c, hc⟩ := ((h2.mul ha).mul hb)
  have hu : 2 * a * b * ((c⁻¹ : Rˣ) : R) = 1 := by
    rw [← hc]; simp
  set u : R := ((c⁻¹ : Rˣ) : R) with hu_def
  set l : R := (t ^ 2 - a - 1) * u with hl
  refine ⟨⟨ε * t + (1 - ε), ε * (l * b + 1), ε * (l * a * q), ε * (l * p)⟩, ?_, ?_⟩
  · simp only [nrm]
    linear_combination ((t - 1) ^ 2 + (-a * (l * b + 1) ^ 2 - b * (l * a * q) ^ 2 + a * b * (l * p) ^ 2)) * hε
      - ε * (t ^ 2 - a - 1) * hu - l ^ 2 * a * b * hE
  · show ε * (ε * t + (1 - ε)) = ε * t
    linear_combination (t - 1) * hε

end GlobalTheory
