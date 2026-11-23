import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipLeStabP

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.UnipEv

theorem evalZero_inv_after_stab : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (i₀ i₁ : ℕ) (M₁ : Model σ X W₁) (om₁ : Rep σ X W₁) (r₁ s₁ : ℕ),
      H'.IsAdapted σ B W W₁ i₀ i₁ → IsPair B M₁ χX χW om₁ r s r₁ s₁ → ∀ e, IsEv B M M₁ 1 H'.ι (iso0 n H') e →
      ∀ g ∈ GlobalTheory.UnipEv.stabilizer₂ σ W H', ∀ u ∈ iso0 n H', ∀ Φ ∈ schA F (Fin n × Fin d), e (om (1, g) (M.co.rho B.ψ u Φ)) = e (om (1, g) Φ) := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP d₁ W₁ H' i₀ i₁ M₁ om₁ r₁ s₁ hA hP₁ e he g hg u hu Φ hΦ
  have hs := IsUWeilPair.isUSplitting hP.weil
  obtain ⟨y, rfl⟩ := hu
  obtain ⟨⟨t, ht⟩, -⟩ := hg
  rw [hs.impl (1, g) _ Φ hΦ]
  have key : actAB (cA σ) ((1, g) : UA σ X.J × UA σ W.J) (Matrix.vecMulVec y (incV F H'.x)) =
      Matrix.vecMulVec (fun i => y i * (t : AE F E)) (incV F H'.x) := by
    have h1 : actAB (cA σ) ((1, g) : UA σ X.J × UA σ W.J) (Matrix.vecMulVec y (incV F H'.x)) =
        Matrix.vecMulVec y (incV F H'.x) * (mat g)ᵀ := by
      simp [actAB, mat]
    rw [h1, Matrix.vecMulVec_mul, Matrix.vecMul_transpose, ht]
    ext i j
    simp [Matrix.vecMulVec_apply, mul_assoc, mul_comm, mul_left_comm]
  rw [key, he.inv _ ⟨_, rfl⟩ _ (hs.pres _ _ hΦ)]

end GlobalTheory.UnipEv
