import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SetIntegralEqZeroOfMulRight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedEvaluationNonvanishing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenIntertwinerRestrictionPairStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.ThK.IsoStep

open GlobalTheory.ThK.UnipDom GlobalTheory.ThK.UnipDom.Inverse GlobalTheory.ThK.IsoZero

theorem ev_step : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d d₁ : ℕ) (X : Spc F E n) (W : Spc F E d) (W₁ : Spc F E d₁) (M : Model σ X W) (M₁ : Model σ X W₁) (H' : Plane E d d₁) (i₀ i₁ : ℕ),
    H'.IsAdapted σ B W W₁ i₀ i₁ → M₁.IsGood B.ψ → ∀ (e₀ : Fn F n d →ₗ[ℂ] Fn F n d₁), IsEv B M M₁ 1 H'.ι (iso0 n H') e₀ →
    ∀ (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (n₁ : ℕ) (X₁ : Spc F E n₁) (H : Plane E n n₁) (j₀ j₁ : ℕ), H.IsAdapted σ B X X₁ j₀ j₁ →
    ∀ u ∈ unip σ W H', ∀ (z : Fin d₁ → AE F E) (β : AE F E),
      mat u⁻¹ *ᵥ incV F H'.y = incV F H'.y + incM F H'.ι *ᵥ z + β • incV F H'.x → ∀ Ψ ∈ schA F (Fin n × Fin d),
      e₀ (M.co.rho B.ψ (Matrix.vecMulVec (incV F H.x) (incV F H'.y)) (om (1, u) Ψ)) =
        M₁.co.rho B.ψ (Matrix.vecMulVec (incV F H.x) z) (e₀ (M.co.rho B.ψ (Matrix.vecMulVec (incV F H.x) (incV F H'.y)) Ψ)) := by
  intro hKP F E _ _ _ _ _ σ B n d d₁ X W W₁ M M₁ H' i₀ i₁ hH' hM₁ e₀ he₀ χX χW om r s r' s' hP n₁ X₁ H j₀ j₁ hH
    u hu z β hv Ψ hΨ
  have hstd : IsStd B.ψ := hP.base.std
  have hsch : ∀ γ, ∀ Φ ∈ schA F (Fin n × Fin d), M.co.rho B.ψ γ Φ ∈ schA F (Fin n × Fin d) :=
    fun γ Φ hΦ => GlobalTheory.HeisSchA.rho_mem_schA M B.ψ hstd γ Φ hΦ
  have ha' : mat u⁻¹ *ᵥ incV F H'.y = β • incV F H'.x + incM F H'.ι *ᵥ z + incV F H'.y := by
    rw [hv]; abel
  have hrho : ∀ (p q : Fin d → AE F E) (φ : Fn F n d),
      M.co.rho B.ψ (Matrix.vecMulVec (incV F H.x) p) (M.co.rho B.ψ (Matrix.vecMulVec (incV F H.x) q) φ) =
        M.co.rho B.ψ (Matrix.vecMulVec (incV F H.x) (p + q)) φ := fun p q φ => by
    rw [rho_rho M.co B.ψ _ _ (symp_iso σ X.J W.J H.x hH.xx p q), vmv_add]
  have himpl := (IsUWeilPair.isUSplitting hP.weil).impl ((1 : UA σ X.J), u)
    (Matrix.vecMulVec (incV F H.x) (mat u⁻¹ *ᵥ incV F H'.y)) Ψ hΨ
  have hact : actAB (cA σ) ((1 : UA σ X.J), u) (Matrix.vecMulVec (incV F H.x) (mat u⁻¹ *ᵥ incV F H'.y)) =
      Matrix.vecMulVec (incV F H.x) (incV F H'.y) := by
    show (1 : Matrix (Fin n) (Fin n) (AE F E)) * _ * (mat u)ᵀ = _
    rw [Matrix.one_mul, vmv_mul_transpose, Matrix.mulVec_mulVec, ← GlobalTheory.ThK.UnipDom.Inverse.mat_mul, mul_inv_cancel,
      GlobalTheory.ThK.UnipDom.Inverse.mat_one, Matrix.one_mulVec]
  rw [hact] at himpl
  have hI : incM F (1 : Matrix (Fin n) (Fin n) E) = 1 := Matrix.map_one _ (map_zero _) (map_one _)
  have hΨA := hsch (Matrix.vecMulVec (incV F H.x) (incV F H'.y)) Ψ hΨ
  have hΨB := hsch (Matrix.vecMulVec (incV F H.x) (incM F H'.ι *ᵥ z)) _ hΨA
  calc e₀ (M.co.rho B.ψ (Matrix.vecMulVec (incV F H.x) (incV F H'.y)) (om (1, u) Ψ))
      = e₀ (om (1, u) (M.co.rho B.ψ (Matrix.vecMulVec (incV F H.x) (mat u⁻¹ *ᵥ incV F H'.y)) Ψ)) := by
        rw [himpl]
    _ = e₀ (M.co.rho B.ψ (Matrix.vecMulVec (incV F H.x) (mat u⁻¹ *ᵥ incV F H'.y)) Ψ) := by
        rw [GlobalTheory.T.eigen_intertwiner_restriction_pair hKP F E σ B n d d₁ X W W₁ M M₁ H' i₀ i₁ hH' hM₁ e₀ he₀ χX χW om r s r' s' hP u hu _
          (hsch _ Ψ hΨ)]
    _ = e₀ (M.co.rho B.ψ (Matrix.vecMulVec (incV F H.x) (β • incV F H'.x))
          (M.co.rho B.ψ (Matrix.vecMulVec (incV F H.x) (incM F H'.ι *ᵥ z))
            (M.co.rho B.ψ (Matrix.vecMulVec (incV F H.x) (incV F H'.y)) Ψ))) := by
        rw [hrho, hrho, ha']
    _ = e₀ (M.co.rho B.ψ (Matrix.vecMulVec (incV F H.x) (incM F H'.ι *ᵥ z))
          (M.co.rho B.ψ (Matrix.vecMulVec (incV F H.x) (incV F H'.y)) Ψ)) := by
        rw [he₀.inv _ ⟨β • incV F H.x, vmv_smul_right _ _ _⟩ _ hΨB]
    _ = M₁.co.rho B.ψ (Matrix.vecMulVec (incV F H.x) z)
          (e₀ (M.co.rho B.ψ (Matrix.vecMulVec (incV F H.x) (incV F H'.y)) Ψ)) := by
        rw [← he₀.Heisenberg₂ _ _ hΨA, hI, Matrix.one_mul, ← vmv_mulVec]

end GlobalTheory.ThK.IsoStep
