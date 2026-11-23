import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianAdaptedPlaneRestrictionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianAdaptedPlaneThetaIntegralStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianAdaptedPlaneLocalFactorStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.MixXLevi

theorem evalZero_levi : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (n₁ : ℕ) (X₁ : Spc F E n₁) (H : Plane E n n₁) (j₀ j₁ : ℕ) (M₁ : Model σ X₁ W) (om₁ : Rep σ X₁ W) (r₁ s₁ : ℕ),
      H.IsAdapted σ B X X₁ j₀ j₁ → IsPair B M₁ χX χW om₁ r₁ s₁ r' s' →
      ∀ e, IsEv B M M₁ H.ι 1 {u | ∃ z, u = Matrix.vecMulVec (incV F H.x) z} e →
      ∀ (t : (AE F E)ˣ) (g₁ : UA σ X₁.J) (m : UA σ X.J), IsLevi H t g₁ m → ∀ Φ ∈ schA F (Fin n × Fin d),
        e (om (m, 1) Φ) = ((χW t : ℂ) * (((absE F E t : ℝ) ^ ((d : ℝ) / 2) : ℝ) : ℂ)) • om₁ (g₁, 1) (e Φ) := by
  intro hPr F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP n₁ X₁ H j₀ j₁ M₁ om₁ r₁ s₁ hH hP₁ e he t g₁ m hm Φ hΦ
  obtain ⟨mt, hmt⟩ := GlobalTheory.T.hermitian_adapted_plane_restriction hPr F E σ B n d X W M χX χW om r s r' s' hP n₁ X₁ H j₀ j₁ M₁ om₁ r₁ s₁ hH hP₁ t
  have hinv : mat mt⁻¹ * mat mt = 1 := by
    show ((mt⁻¹ : UA σ X.J).1.1) * mt.1.1 = 1
    rw [← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel]; rfl
  have hmul : mat (mt⁻¹ * m) = mat mt⁻¹ * mat m := rfl
  have hone : mat (1 : UA σ X₁.J) = 1 := rfl
  have hcA : cA σ t.1 * cA σ (t⁻¹ : (AE F E)ˣ).1 = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  obtain ⟨hx, hy, hι⟩ := hm
  obtain ⟨hx', hy', hι'⟩ := hmt
  have key : IsLevi H 1 g₁ (mt⁻¹ * m) := by
    have ex : mat mt⁻¹ *ᵥ incV F H.x = (t⁻¹ : (AE F E)ˣ).1 • incV F H.x := by
      have h1 : t.1 • (mat mt⁻¹ *ᵥ incV F H.x) = incV F H.x := by
        rw [← Matrix.mulVec_smul, ← hx', Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]
      calc mat mt⁻¹ *ᵥ incV F H.x = (t⁻¹ : (AE F E)ˣ).1 • (t.1 • (mat mt⁻¹ *ᵥ incV F H.x)) := by
            rw [smul_smul, Units.inv_mul, one_smul]
        _ = _ := by rw [h1]
    have ey : mat mt⁻¹ *ᵥ incV F H.y = cA σ t.1 • incV F H.y := by
      have h1 : cA σ (t⁻¹ : (AE F E)ˣ).1 • (mat mt⁻¹ *ᵥ incV F H.y) = incV F H.y := by
        rw [← Matrix.mulVec_smul, ← hy', Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]
      calc mat mt⁻¹ *ᵥ incV F H.y = cA σ t.1 • (cA σ (t⁻¹ : (AE F E)ˣ).1 • (mat mt⁻¹ *ᵥ incV F H.y)) := by
            rw [smul_smul, hcA, one_smul]
        _ = _ := by rw [h1]
    have eι : mat mt⁻¹ * incM F H.ι = incM F H.ι := by
      have h1 : mat mt * incM F H.ι = incM F H.ι := by rw [hι', hone, Matrix.mul_one]
      calc mat mt⁻¹ * incM F H.ι = mat mt⁻¹ * (mat mt * incM F H.ι) := by rw [h1]
        _ = _ := by rw [← Matrix.mul_assoc, hinv, Matrix.one_mul]
    refine ⟨?_, ?_, ?_⟩
    · rw [hmul, ← Matrix.mulVec_mulVec, hx, Matrix.mulVec_smul, ex, smul_smul, Units.mul_inv, Units.val_one]
    · rw [hmul, ← Matrix.mulVec_mulVec, hy, Matrix.mulVec_smul, ey, smul_smul, mul_comm, hcA, inv_one, Units.val_one,
        map_one]
    · rw [hmul, Matrix.mul_assoc, hι, ← Matrix.mul_assoc, eι]
  have hsp := (IsUWeilPair.isUSplitting hP.weil).pres
  have hpair : ((m, 1) : UA σ X.J × UA σ W.J) = (mt, 1) * (mt⁻¹ * m, 1) :=
    Prod.ext (mul_inv_cancel_left mt m).symm (mul_one 1).symm
  rw [hpair, map_mul, Module.End.mul_apply]
  rw [GlobalTheory.T.hermitian_adapted_plane_theta_integral hPr F E σ B n d X W M χX χW om r s r' s' hP n₁ X₁ H j₀ j₁ M₁ om₁ r₁ s₁ hH hP₁ e he t mt ⟨hx', hy', hι'⟩ _ (hsp _ _ hΦ)]
  rw [GlobalTheory.T.hermitian_adapted_plane_local_factor hPr F E σ B n d X W M χX χW om r s r' s' hP n₁ X₁ H j₀ j₁ M₁ om₁ r₁ s₁ hH hP₁ e he g₁ _ key Φ hΦ]

end GlobalTheory.MixXLevi
