import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section
namespace GlobalTheory.ThK.IsoSymp

theorem sigma_sigma {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (e : E) : σ (σ e) = e := by
  have τ : E →+* ℂ := (IsAlgClosed.lift (M := ℂ) (R := ℚ) (S := E)).toRingHom
  apply τ.injective
  rw [h.2.2.2, h.2.2.2, star_star]

theorem cA_inclR {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) (e : E) :
    cA σ (inclR (AF F) e) = inclR (AF F) (σ e) := by
  simp [cA, inclR, Algebra.TensorProduct.includeRight_apply]

theorem form_swap {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} (hσ : ∀ e, σ (σ e) = e) {d : ℕ} (J : Matrix (Fin d) (Fin d) E)
    (hJ : ∀ i j, σ (J j i) = -J i j) (x y : Fin d → E) :
    σ (form σ J x y) = - form σ J y x := by
  simp only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, hσ, hJ, Finset.mul_sum, ← Finset.sum_neg_distrib]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem symp_iso_term : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d d₁ : ℕ) (X : Spc F E n) (W : Spc F E d) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (i₀ i₁ r s r' s' : ℕ), B.IsGood σ → X.IsHerm σ B r s → W.IsSkew σ B r' s' → H'.IsAdapted σ B W W₁ i₀ i₁ → ∀ (ξ : Fin n → E) (y : Fin n → AE F E), symp (cA σ) (-1) (incM F X.J) (incM F W.J) (Matrix.vecMulVec (incV F ξ) (incV F H'.y)) (Matrix.vecMulVec y (incV F H'.x)) = Algebra.trace (AF F) (AE F E) (∑ i, incV F ξ i * (incM F X.J *ᵥ fun k => cA σ (y k)) i) := by
  intro F E _ _ _ _ _ σ B n d d₁ X W W₁ H' i₀ i₁ r s r' s' hB hX hW hH ξ y
  have hσ : ∀ e, σ (σ e) = e := sigma_sigma hB.cm
  have hf : form σ W.J H'.y H'.x = -1 := by
    have h1 := form_swap hσ W.J hW.skew H'.x H'.y
    rw [hH.xy, map_one] at h1
    linear_combination h1
  have key : hTens (cA σ) (incM F X.J) (incM F W.J) (Matrix.vecMulVec (incV F ξ) (incV F H'.y))
      (Matrix.vecMulVec y (incV F H'.x)) =
      (∑ i, incV F ξ i * (incM F X.J *ᵥ fun k => cA σ (y k)) i) * inclR (AF F) (form σ W.J H'.y H'.x) := by
    simp only [hTens, Matrix.vecMulVec_apply, incV, incM, Matrix.map_apply, map_mul, cA_inclR]
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm, Matrix.mulVec, dotProduct, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, Finset.mul_sum, Matrix.map_apply]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
    ring
  rw [symp, key, hf, map_neg, map_one]
  congr 1
  ring

end GlobalTheory.ThK.IsoSymp
end
