import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisAtMinusRho
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoreConcl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTransv
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsAHEqOfMemRatPts
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EisensteinIsotropicLine
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisensteinSettingHeightContinuousStatement
open scoped TensorProduct NNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.EisRes
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.EisRes

open scoped Pointwise

theorem iwaHt_mul_le_of_isCompact : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ)
    (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E) (L : Submodule (𝓞 E) (Fin n → E))
    (a : GL (Fin n) (AF F ⊗[F] E)) (h : GAd σ J → ℝ), HidaSetting σ J X Y L a h →
    ∀ C : Set (GAd σ J), IsCompact C → ∃ K : ℝ, 0 ≤ K ∧ ∀ γ g, g ∈ C → h (γ * g) ≤ K * h γ := by
  intro F E _ _ _ _ _ σ n J r X Y L a h hS C hC
  have hcont : Continuous h := GlobalTheory.T.eisenstein_setting_height_continuous F E σ n J r X Y L a h hS
  obtain ⟨hCM, -, -, -, -, hAd, hI⟩ := hS
  haveI := hAd.lat
  have hK : IsCompact ((levelAll σ J L a : Set (GAd σ J)) * C) :=
    (GlobalTheory.Doubling.isCompact_levelAll hCM J L a).mul hC
  obtain ⟨K0, hK0⟩ := hK.exists_bound_of_continuousOn hcont.continuousOn
  refine ⟨max K0 0, le_max_right _ _, fun γ g hg => ?_⟩
  obtain ⟨p, l, hp, k, hk, rfl⟩ := hI.1 γ
  obtain ⟨p', l', hp', k', hk', hkg⟩ := hI.1 (k * g)
  have e1 : p * k * g = (p * p') * k' := by rw [mul_assoc, hkg, mul_assoc]
  have hpp : (matHom _ σ J (p * p')).1 * adMat F (col0 X) = (l * l').1 • adMat F (col0 X) := by
    rw [map_mul, Units.val_mul, Matrix.mul_assoc, hp', Matrix.mul_smul, hp, smul_smul, Units.val_mul, mul_comm (l' : AF F ⊗[F] E)]
  have h1 : h (p * k * g) = absE F E (l * l') := by rw [e1]; exact hI.2 _ _ hpp _ hk'
  have h2 : h (p * k) = absE F E l := hI.2 _ _ hp _ hk
  have h3 : h (k * g) = absE F E l' := by rw [hkg]; exact hI.2 _ _ hp' _ hk'
  have hb : h (k * g) ≤ max K0 0 :=
    ((le_abs_self _).trans (by simpa [Real.norm_eq_abs] using hK0 _ (Set.mul_mem_mul hk hg))).trans (le_max_left _ _)
  rw [h1, h2, map_mul, NNReal.coe_mul, mul_comm (absE F E l : ℝ)]
  exact mul_le_mul_of_nonneg_right (h3 ▸ hb) (NNReal.coe_nonneg _)

end GlobalTheory.EisRes
