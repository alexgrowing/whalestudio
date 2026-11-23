import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsGauss
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaussNormExtensionAcris
import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics
open GlobalTheory.PMon.Gauss
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.PMon.Gauss

lemma gA_term_le_one (l : ℕ) [Fact l.Prime] (ρ : ℝ) (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1) (a : Formalism.Per.Ainf l) (n : ℕ) :
    ‖(((a.coeff n).untilt : Formalism.Per.OC l) : ℂ_[l])‖ ^ ((1 : ℝ) / (l : ℝ) ^ n) * ρ ^ n ≤ 1 := by
  have hx0 : 0 ≤ ‖(((a.coeff n).untilt : Formalism.Per.OC l) : ℂ_[l])‖ := norm_nonneg _
  have hx1 : ‖(((a.coeff n).untilt : Formalism.Per.OC l) : ℂ_[l])‖ ≤ 1 := (GlobalTheory.RingBasics.mem_OC _).1 ((a.coeff n).untilt).2
  have he : 0 ≤ (1 : ℝ) / (l : ℝ) ^ n := by positivity
  have h2 : ‖(((a.coeff n).untilt : Formalism.Per.OC l) : ℂ_[l])‖ ^ ((1 : ℝ) / (l : ℝ) ^ n) ≤ 1 :=
    Real.rpow_le_one hx0 hx1 he
  have h3 : ρ ^ n ≤ 1 := pow_le_one₀ h0 h1
  calc _ ≤ 1 * 1 := mul_le_mul h2 h3 (pow_nonneg h0 n) zero_le_one
    _ = 1 := one_mul 1

theorem gC_teich_sub_eq_one : ∀ (l : ℕ) [Fact l.Prime] (ζ ζ' : Formalism.Per.Fl l),
    ‖(((ζ - ζ').untilt : Formalism.Per.OC l) : ℂ_[l])‖ = 1 →
      ∀ ρ : ℝ, (l : ℝ)⁻¹ ≤ ρ → ρ < 1 → gC l ρ (tc l ζ - tc l ζ') = 1 := by
  intro l _ ζ ζ' hζ ρ hρ hρ1
  have hex : ∃ N, IsGauss l ρ N := GlobalTheory.GaussExt.exists_gauss_acris l ρ hρ hρ1
  have hg : IsGauss l ρ (Classical.choose hex) := Classical.choose_spec hex
  have hC : gC l ρ (tc l ζ - tc l ζ') = Classical.choose hex (tc l ζ - tc l ζ') := by
    unfold gC; rw [dif_pos hex]
  have hsub : tc l ζ - tc l ζ' =
      algebraMap (Formalism.Per.Ainf l) (Formalism.Per.Acris l) (Formalism.Per.tm ζ - Formalism.Per.tm ζ') := by
    unfold tc; rw [map_sub]
  rw [hC, hsub, hg.2.2.2.2]
  have hl : (0 : ℝ) < (l : ℝ)⁻¹ := by
    have : (0 : ℝ) < (l : ℝ) := by exact_mod_cast (Fact.out : l.Prime).pos
    positivity
  have h0 : 0 ≤ ρ := le_of_lt (lt_of_lt_of_le hl hρ)
  have hc0 : (Formalism.Per.tm ζ - Formalism.Per.tm ζ').coeff 0 = ζ - ζ' := by
    have := map_sub (WittVector.constantCoeff (p := l) (R := Formalism.Per.Fl l)) (Formalism.Per.tm ζ) (Formalism.Per.tm ζ')
    simpa [Formalism.Per.tm] using this
  unfold gA
  apply le_antisymm
  · exact ciSup_le (fun n => gA_term_le_one l ρ h0 hρ1.le _ n)
  · have hb : BddAbove (Set.range fun n : ℕ =>
        ‖((((Formalism.Per.tm ζ - Formalism.Per.tm ζ').coeff n).untilt : Formalism.Per.OC l) : ℂ_[l])‖ ^
          ((1 : ℝ) / (l : ℝ) ^ n) * ρ ^ n) :=
      ⟨1, by rintro _ ⟨n, rfl⟩; exact gA_term_le_one l ρ h0 hρ1.le _ n⟩
    refine le_trans ?_ (le_ciSup hb 0)
    simp [hc0, hζ]

end GlobalTheory.PMon.Gauss

end
