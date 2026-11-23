import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixExtendByZeroAdd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatRestrictionAndProduct
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyIntegralPointsIndicatorIsVacuum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchrodingerTensorEqLocalOfSupportedAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AddCharHalfTraceTensorLatticeHeisenbergCocycle
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntAddConjEqOneOfBaseGood
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PosHomApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSchwartzNe
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.AdaptEv
open scoped GlobalTheory.VacAny

noncomputable section

namespace GlobalTheory.AdaptGram

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem incM_gram (σ : E →ₐ[F] E) {n m : ℕ} (A : Matrix (Fin n) (Fin m) E) (J : Matrix (Fin n) (Fin n) E) :
    (incM F A)ᵀ * incM F J * (incM F A).map (cA σ) = incM F (Aᵀ * J * A.map σ) := by
  have h : (incM F A).map (cA σ) = incM F (A.map σ) := by ext i j; rfl
  rw [h]
  simp only [incM, Matrix.transpose_map, Matrix.map_mul]

theorem hTens_adapted : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    {n d n₁ d₁ : ℕ} (X : Spc F E n) (W : Spc F E d) (X₁ : Spc F E n₁) (W₁ : Spc F E d₁) (H : Plane E n n₁) (H' : Plane E d d₁) (i₀ i₁ j₀ j₁ : ℕ), H.IsAdapted σ B X X₁ j₀ j₁ → H'.IsAdapted σ B W W₁ i₀ i₁ →
    ∀ g g' : Matrix (Fin n₁) (Fin d₁) (AE F E),
      hTens (cA σ) (incM F X.J) (incM F W.J) (incM F H.ι * g * (incM F H'.ι)ᵀ) (incM F H.ι * g' * (incM F H'.ι)ᵀ) =
        hTens (cA σ) (incM F X₁.J) (incM F W₁.J) g g' := by
  intro F E _ _ _ _ _ σ B n d n₁ d₁ X W X₁ W₁ H H' i₀ i₁ j₀ j₁ hH hH' g g'
  rw [GlobalTheory.ThK.Adapt.hTens_mul, incM_gram, incM_gram, hH.gram, hH'.gram]

end GlobalTheory.AdaptGram
