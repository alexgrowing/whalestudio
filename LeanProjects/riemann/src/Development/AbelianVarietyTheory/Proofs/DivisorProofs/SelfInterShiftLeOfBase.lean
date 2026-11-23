import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsModelOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormHeightExpSmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsImageHeightUnique
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical

namespace GlobalTheory.SelfInterImage

theorem imageHeight_exp_smul {K V Ω : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] [Field Ω] [Algebra K Ω] {Nm : (K →+* ℂ) → V → ℝ} {W : Submodule (𝓞 K) V}
    {ev : V →ₗ[K] Ω} {D : ℕ} (hex : ∃ x, IsImageHeight Nm W ev D x) (t : ℝ) :
    imageHeight (fun σ x => Real.exp (-t) * Nm σ x) W ev D = imageHeight Nm W ev D + t := by
  have h1 := GlobalTheory.HeightShift.isImageHeight_shift K V Ω Nm W ev D _ (fun _ => t) (fun _ => rfl)
    (isImageHeight_imageHeight hex)
  have e : (∑ _σ : K →+* ℂ, t) / (Module.finrank ℚ K : ℝ) = t := by
    rw [Finset.sum_const, Finset.card_univ, NumberField.Embeddings.card, nsmul_eq_mul]
    have : (Module.finrank ℚ K : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Module.finrank_pos.ne'
    field_simp
  rw [e] at h1
  exact GlobalTheory.ImageHeightUnique.isImageHeight_unique (isImageHeight_imageHeight ⟨_, h1⟩) h1

end GlobalTheory.SelfInterImage
