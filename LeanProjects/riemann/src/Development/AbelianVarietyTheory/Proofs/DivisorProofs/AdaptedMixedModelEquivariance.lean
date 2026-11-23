import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvaluationMapAdaptedPlaneContinuous

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.ThetaExpandXInv

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem incM_mul_one {n n₁ d₁ : ℕ} (ι : Matrix (Fin n) (Fin n₁) E) (U : Matrix (Fin n₁) (Fin d₁) E) :
    incM F (ι * U) = incM F ι * incM F U * (incM F (1 : Matrix (Fin d₁) (Fin d₁) E))ᵀ := by
  have h1 : incM F (1 : Matrix (Fin d₁) (Fin d₁) E) = 1 :=
    Matrix.map_one _ (map_zero _) (map_one _)
  rw [h1, Matrix.transpose_one, Matrix.mul_one]
  unfold incM
  rw [Matrix.map_mul]

theorem exists_split_left {n n₁ d₁ : ℕ} {X : Spc F E n} {X₁ : Spc F E n₁} {B : Base F E} {H : Plane E n n₁} {j₀ j₁ : ℕ}
    (hH : H.IsAdapted σ B X X₁ j₀ j₁) (hL : X.L.IsLattice E) (x : Matrix (Fin n) (Fin d₁) E) :
    ∃ (s t : Fin d₁ → E) (U : Matrix (Fin n₁) (Fin d₁) E),
      x = Matrix.vecMulVec H.x s + H.ι * U + Matrix.vecMulVec H.y t := by
  obtain ⟨s, t, U, h⟩ := GlobalTheory.ThetaExpandInv.exists_split (n := d₁) hH hL xᵀ
  refine ⟨s, t, Uᵀ, ?_⟩
  have h' := congrArg Matrix.transpose h
  simp only [Matrix.transpose_transpose, Matrix.transpose_add, Matrix.transpose_mul,
    Matrix.transpose_vecMulVec] at h'
  exact h'

theorem main : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d₁ : ℕ) (X : Spc F E n) (W₁ : Spc F E d₁) (M₁ : Model σ X W₁), M₁.IsGood B.ψ →
    ∀ (n₁ : ℕ) (X₁ : Spc F E n₁) (H : Plane E n n₁) (j₀ j₁ : ℕ) (M₂ : Model σ X₁ W₁), H.IsAdapted σ B X X₁ j₀ j₁ → M₂.IsGood B.ψ →
    ∀ e' : Fn F n d₁ →ₗ[ℂ] Fn F n₁ d₁, IsEv B M₁ M₂ H.ι 1 {u | ∃ z, u = Matrix.vecMulVec (incV F H.x) z} e' → B.IsGood σ →
    (∃ r s r' s' : ℕ, X.IsHerm σ B r s ∧ W₁.IsSkew σ B r' s') →
    ∀ x : Matrix (Fin n) (Fin d₁) E, ∀ φ ∈ schA F (Fin n × Fin d₁), (∑' w : Fin d₁ → E, thetaSum F (e' (M₁.co.rho B.ψ (Matrix.vecMulVec (incV F H.y) (incV F w)) (M₁.co.rho B.ψ (incM F x) φ)))) = (∑' w : Fin d₁ → E, thetaSum F (e' (M₁.co.rho B.ψ (Matrix.vecMulVec (incV F H.y) (incV F w)) (φ)))) := by
  intro _ F E _ _ _ _ _ σ B n d₁ X W₁ M₁ hM₁ n₁ X₁ H j₀ j₁ M₂ hH hM₂ e' he hB hsig x φ hφ
  obtain ⟨r, s, r', s', hX, -⟩ := hsig
  have hψ : IsStd B.ψ := hB.std
  obtain ⟨a, t, U, hx⟩ := exists_split_left hH hX.lat x
  have key : ∀ w : Fin d₁ → E,
      thetaSum F (e' (M₁.co.rho B.ψ (Matrix.vecMulVec (incV F H.y) (incV F w)) (M₁.co.rho B.ψ (incM F x) φ))) =
        thetaSum F (e' (M₁.co.rho B.ψ (Matrix.vecMulVec (incV F H.y) (incV F (w + t))) φ)) := by
    intro w
    have hsum : Matrix.vecMulVec H.y w + x =
        Matrix.vecMulVec H.x a + (H.ι * U + Matrix.vecMulVec H.y (w + t)) := by
      rw [hx, Matrix.vecMulVec_add]; abel
    have hiso : incM F (Matrix.vecMulVec H.x a) ∈
        ({u | ∃ z, u = Matrix.vecMulVec (incV F H.x) z} : Set (Matrix (Fin n) (Fin d₁) (AE F E))) :=
      ⟨incV F a, GlobalTheory.ThetaExpandInv.incM_vecMulVec H.x a⟩
    rw [← GlobalTheory.ThetaExpandInv.incM_vecMulVec, GlobalTheory.ThetaExpandInv.rho_rat_rho_rat M₁ hψ hM₁, hsum,
      ← GlobalTheory.ThetaExpandInv.rho_rat_rho_rat M₁ hψ hM₁,
      he.inv _ hiso _ (GlobalTheory.HeisSchA.rho_mem_schA M₁ B.ψ hψ _ φ hφ), ← GlobalTheory.ThetaExpandInv.rho_rat_rho_rat M₁ hψ hM₁,
      incM_mul_one, he.Heisenberg₂ _ _ (GlobalTheory.HeisSchA.rho_mem_schA M₁ B.ψ hψ _ φ hφ),
      GlobalTheory.ThetaExpandInv.thetaSum_rho_rat M₂ hψ hM₂, GlobalTheory.ThetaExpandInv.incM_vecMulVec]
  rw [tsum_congr key]
  exact (Equiv.addRight t).tsum_eq
    (fun w : Fin d₁ → E => thetaSum F (e' (M₁.co.rho B.ψ (Matrix.vecMulVec (incV F H.y) (incV F w)) φ)))

end GlobalTheory.ThetaExpandXInv
