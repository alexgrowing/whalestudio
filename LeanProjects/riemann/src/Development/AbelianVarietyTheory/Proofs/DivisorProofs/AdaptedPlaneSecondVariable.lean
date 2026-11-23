import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewAdaptedPlaneRestrictionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewAdaptedPlaneThetaIntegralStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewAdaptedPlaneLocalFactorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewAdaptedPlaneSeesawIdentityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewAdaptedPlanePairOfPairStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.MixW

theorem evalZero_law : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (i₀ i₁ : ℕ) (M₁ : Model σ X W₁) (om₁ : Rep σ X W₁) (r₁ s₁ : ℕ),
      H'.IsAdapted σ B W W₁ i₀ i₁ → IsPair B M₁ χX χW om₁ r s r₁ s₁ → ∀ e, IsEv B M M₁ 1 H'.ι (iso0 n H') e  →
      ∀ g t h₁ m, IsLevi H' t h₁ m → ∀ u ∈ unip σ W H', ∀ Φ ∈ schA F (Fin n × Fin d),
        e (om (g, u * m) Φ) = ((χX t : ℂ) * (((absE F E t : ℝ) ^ ((n : ℝ) / 2) : ℝ) : ℂ)) • om₁ (g, h₁) (e Φ) := by
  intro hK F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP d₁ W₁ H' i₀ i₁ M₁ om₁ r₁ s₁ hH hP₁ e he g t h₁ m hm u hu Φ hΦ
  have pr : ∀ x, ∀ Ψ ∈ schA F (Fin n × Fin d), om x Ψ ∈ schA F (Fin n × Fin d) :=
    fun x Ψ hΨ => (IsUWeilPair.isUSplitting hP.weil).pres x Ψ hΨ
  obtain ⟨m₁, hm₁⟩ := GlobalTheory.T.skew_adapted_plane_pair_of_pair F E σ B n d X W M χX χW om r s r' s' hP d₁ W₁ H' i₀ i₁ M₁ om₁ r₁ s₁ hH hP₁ t
  have hm₂ : IsLevi H' 1 h₁ (m₁⁻¹ * m) := by
    obtain ⟨a1, a2, a3⟩ := hm
    obtain ⟨b1, b2, b3⟩ := hm₁
    have hmat : ∀ a b : UA σ W.J, mat (a * b) = mat a * mat b := fun a b => rfl
    have hinv : mat m₁⁻¹ * mat m₁ = 1 := by rw [← hmat, inv_mul_cancel]; rfl
    have hone : mat (1 : UA σ W₁.J) = 1 := rfl
    rw [hone, Matrix.mul_one] at b3
    refine ⟨?_, ?_, ?_⟩
    · rw [hmat, ← Matrix.mulVec_mulVec, a1, ← b1, Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec, Units.val_one, one_smul]
    · rw [hmat, ← Matrix.mulVec_mulVec, a2, ← b2, Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec, inv_one, Units.val_one,
        map_one, one_smul]
    · rw [hmat, Matrix.mul_assoc, a3, ← Matrix.mul_assoc, ← b3, ← Matrix.mul_assoc, hinv, Matrix.one_mul, b3]
  have hsplit : m = m₁ * (m₁⁻¹ * m) := by group
  have hlev : e (om (1, m) Φ) = ((χX t : ℂ) * (((absE F E t : ℝ) ^ ((n : ℝ) / 2) : ℝ) : ℂ)) • om₁ (1, h₁) (e Φ) := by
    have h1 : om (1, m) = om (1, m₁) * om (1, m₁⁻¹ * m) := by
      rw [← map_mul]; congr 1; ext <;> simp
    rw [h1, Module.End.mul_apply,
      GlobalTheory.T.skew_adapted_plane_seesaw_identity hK F E σ B n d X W M χX χW om r s r' s' hP d₁ W₁ H' i₀ i₁ M₁ om₁ r₁ s₁ hH hP₁ e he t m₁ hm₁ _ (pr _ _ hΦ),
      GlobalTheory.T.ev_om_levi_eq_om_ev_of_isAdapted hK F E σ B n d X W M χX χW om r s r' s' hP d₁ W₁ H' i₀ i₁ M₁ om₁ r₁ s₁ hH hP₁ e he h₁ _ hm₂ _ hΦ]
  have h2 : om (g, u * m) = om (g, 1) * om (1, u) * om (1, m) := by
    rw [← map_mul, ← map_mul]; congr 1; ext <;> simp
  rw [h2, Module.End.mul_apply, Module.End.mul_apply,
    GlobalTheory.T.skew_adapted_plane_theta_integral hK F E σ B n d X W M χX χW om r s r' s' hP d₁ W₁ H' i₀ i₁ M₁ om₁ r₁ s₁ hH hP₁ e he g _ (pr _ _ (pr _ _ hΦ)),
    GlobalTheory.T.skew_adapted_plane_restriction hK F E σ B n d X W M χX χW om r s r' s' hP d₁ W₁ H' i₀ i₁ M₁ om₁ r₁ s₁ hH hP₁ e he u hu _ (pr _ _ hΦ), hlev,
    map_smul, ← Module.End.mul_apply, ← map_mul]
  congr 3; ext <;> simp

end GlobalTheory.MixW
