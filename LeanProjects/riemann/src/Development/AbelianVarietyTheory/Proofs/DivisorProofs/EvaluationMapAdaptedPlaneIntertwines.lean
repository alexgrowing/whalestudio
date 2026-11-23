import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvaluationMapAdaptedPlaneEquivariantStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchroedingerPreservesAdelicSchwartz
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenIntertwinerTransitive
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaTransformRationalTranslateQuasiInvariant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExpSumCoeffEqZeroOfVanishingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPlaneThetaEmbeddingExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfThetaSumsTranslatesVanishStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.ThKExpandNz

open GlobalTheory.ThetaQuasiRat

theorem main : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d d₁ : ℕ) (X : Spc F E n) (W : Spc F E d) (W₁ : Spc F E d₁) (M : Model σ X W) (M₁ : Model σ X W₁) (H' : Plane E d d₁) (i₀ i₁ : ℕ),
    H'.IsAdapted σ B W W₁ i₀ i₁ → M₁.IsGood B.ψ → ∀ (e₀ : Fn F n d →ₗ[ℂ] Fn F n d₁), IsEv B M M₁ 1 H'.ι (iso0 n H') e₀ → B.IsGood σ → M.IsGood B.ψ → (∃ r s r' s' : ℕ, X.IsHerm σ B r s ∧ W.IsSkew σ B r' s') →
    ∃ Ψ ∈ schA F (Fin n × Fin d), (∑' ξ : Fin n → E, thetaSum F (e₀ (M.co.rho B.ψ (Matrix.vecMulVec (incV F ξ) (incV F H'.y)) (Ψ)))) ≠ 0 := by
  intro hKP F E _ _ _ _ _ σ B n d d₁ X W W₁ M M₁ H' i₀ i₁ hH' hM₁ e₀ he hB hM hXW
  have hstd : IsStd B.ψ := hB.std
  have hρ : ∀ w, ∀ Φ ∈ schA F (Fin n × Fin d), M.co.rho B.ψ w Φ ∈ schA F (Fin n × Fin d) := fun w Φ hΦ =>
    GlobalTheory.SchrKeepsSchA.schr_mem_schA F B.ψ hstd _ _ Φ hΦ
  have hth : ∀ (c : ℂ) (φ : Fn F n d₁), thetaSum F (c • φ) = c * thetaSum F φ := fun c φ => by
    simp only [thetaSum, Pi.smul_apply, smul_eq_mul, tsum_mul_left]

  have hswap : ∀ (a b : (Fin n × Fin d → AF F) × (Fin n × Fin d → AF F)) (φ : Fn F n d),
      schr B.ψ a (schr B.ψ b φ) = B.ψ (a.1 ⬝ᵥ b.2 - b.1 ⬝ᵥ a.2) • schr B.ψ b (schr B.ψ a φ) := by
    intro a b φ
    rw [schr_schr, schr_schr, add_comm b a, smul_smul, ← AddChar.map_add_eq_mul]
    congr 2
    have h2 : ⅟(2 : AF F) * 2 = 1 := invOf_mul_self 2
    linear_combination (a.1 ⬝ᵥ b.2 - b.1 ⬝ᵥ a.2) * h2

  by_contra hcon
  push_neg at hcon

  have hA : ∀ Ψ ∈ schA F (Fin n × Fin d), ∀ ξ : Fin n → E,
      thetaSum F (e₀ (M.co.rho B.ψ (Matrix.vecMulVec (incV F ξ) (incV F H'.y)) Ψ)) = 0 := by
    intro Ψ hΨ
    obtain ⟨N, emb, lam, hinj, hexp⟩ := GlobalTheory.T.adapted_plane_theta_embedding_exists F E σ B n d d₁ X W W₁ M H' i₀ i₁ hH' hB hM hXW
    refine GlobalTheory.T.exp_sum_coeff_eq_zero_of_vanishing N (Fin n → E) lam _ hinj (GlobalTheory.T.evaluation_map_adapted_plane_equivariant hKP F E σ B n d d₁ X W W₁ M M₁ H' i₀ i₁ hH' hM₁ e₀ he hB hM hXW Ψ hΨ) ?_
    intro t
    have h0 := hcon _ (hρ (Matrix.vecMulVec (emb t) (incV F H'.x)) Ψ hΨ)
    rw [← h0]
    refine tsum_congr fun ξ => ?_
    have hinv := he.inv (Matrix.vecMulVec (emb t) (incV F H'.x)) ⟨emb t, rfl⟩ _
      (hρ (Matrix.vecMulVec (incV F ξ) (incV F H'.y)) Ψ hΨ)
    simp only [Darboux.rho] at hinv ⊢
    rw [hswap, LinearMap.map_smul, hinv, hth, hexp, mul_comm]

  have hB0 : ∀ Ψ ∈ schA F (Fin n × Fin d), thetaSum F (e₀ Ψ) = 0 := by
    intro Ψ hΨ
    have h := hA Ψ hΨ 0
    have h1 : Matrix.vecMulVec (incV F (0 : Fin n → E)) (incV F H'.y) = 0 := by
      ext i j
      simp [incV, Matrix.vecMulVec_apply]
    have h2 : M.co.rho B.ψ 0 Ψ = Ψ := by
      funext x
      simp [Darboux.rho, schr]
    rwa [h1, h2] at h

  have hC : ∀ Ψ ∈ schA F (Fin n × Fin d), ∀ x y : Fin n × Fin d₁ → AF F, thetaSum F (schr B.ψ (x, y) (e₀ Ψ)) = 0 := by
    intro Ψ hΨ x y
    have h := he.Heisenberg₂ (M₁.co.e.symm (x, y)) Ψ hΨ
    simp only [Darboux.rho, LinearEquiv.apply_symm_apply] at h
    rw [← h]
    exact hB0 _ (hρ _ Ψ hΨ)
  obtain ⟨Ψ, hΨ, hne⟩ := GlobalTheory.EvNonzero.exists_mem_schA_ev_ne_zero F E σ B n d n d₁ X W X W₁ M M₁ 1 H'.ι (iso0 n H') e₀ hM hM₁ he
  exact hne (GlobalTheory.T.eq_zero_of_theta_sums_translates_vanish F B.ψ hstd _ (e₀ Ψ) (he.maps Ψ hΨ) (hC Ψ hΨ))

end GlobalTheory.ThKExpandNz

end
