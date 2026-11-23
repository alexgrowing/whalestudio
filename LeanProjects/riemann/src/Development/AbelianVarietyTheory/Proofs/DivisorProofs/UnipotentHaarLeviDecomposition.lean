import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviUnipotentHaarModulusStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousCA
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSplitBasisCompl

open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.LeviConjOne

theorem lintegral_mul_levi_one : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n n₁ : ℕ) (X Y : Spc F E n) (X₁ : Spc F E n₁) (H : Plane E n n₁) (r s i₀ i₁ : ℕ), B.IsGood σ → X.IsHerm σ B r s → (reS X Y).IsHerm σ B r s → H.IsAdapted σ B (reS X Y) X₁ i₀ i₁ → ∀ m : (AE F E)ˣ → UA σ X₁.J → UA σ X.J, (∀ l g₀, IsLevi (W₁ := X₁) H l g₀ (m l g₀)) → ∀ μN : Measure (unip σ X H), μN.IsHaarMeasure → ∀ (g₀ : UA σ X₁.J) (f : UA σ X.J → ℝ≥0∞), Measurable f → ∫⁻ u, f (u.1 * m 1 g₀) ∂μN = ∫⁻ u, f (m 1 g₀ * u.1) ∂μN := by
  intro F E _ _ _ _ _ σ B n n₁ X Y X₁ H r s i₀ i₁ hB _ hXY hH m hm μN hμ g₀ f hf
  have hX₁ : X₁.IsHerm σ B (r - 1) (s - 1) := GlobalTheory.HermPlaneCompl.isHerm_compl hB hXY hH
  obtain ⟨hTG, hLCU, hSCU, hT2U⟩ := GlobalTheory.LeviModulus.topUA σ X.J
  haveI := hTG; haveI := hLCU; haveI := hSCU; haveI := hT2U
  haveI : BorelSpace (UA σ X.J) := ⟨rfl⟩
  have hf' : Measurable fun x : UA σ X.J => f (x * m 1 g₀) :=
    hf.comp (continuous_id.mul continuous_const).measurable
  have key : ∫⁻ u, f (m 1 g₀ * u.1 * (m 1 g₀)⁻¹ * m 1 g₀) ∂μN =
      ENNReal.ofReal ((absE F E 1 : ℝ) ^ (1 - (n : ℝ))) * ∫⁻ u, f (u.1 * m 1 g₀) ∂μN :=
    GlobalTheory.T.levi_unipotent_haar_modulus F E σ B n n₁ (reS X Y) X₁ r s (r - 1) (s - 1) i₀ i₁ H hB hXY hX₁ hH m hm μN hμ 1 g₀
      (fun x : UA σ X.J => f (x * m 1 g₀)) hf'
  simp only [map_one, NNReal.coe_one, Real.one_rpow, ENNReal.ofReal_one, one_mul, inv_mul_cancel_right] at key
  exact key.symm

end GlobalTheory.LeviConjOne

end
