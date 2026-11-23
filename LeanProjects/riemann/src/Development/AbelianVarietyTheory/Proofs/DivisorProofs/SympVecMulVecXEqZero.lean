import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TrPApply
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ArchSch

namespace GlobalTheory.LagIsotropic

theorem hTens_vecMulVec_eq_zero {R A : Type} [CommRing R] [CommRing A] [Algebra R A] (c : A →ₐ[R] A)
    {α β : Type} [Fintype α] [Fintype β] (JA : Matrix α α A) (JB : Matrix β β A) (a b : α → A) (x : β → A)
    (hx : ∑ j, ∑ l, x j * JB j l * c (x l) = 0) :
    ∑ i, ∑ j, ∑ k, ∑ l, Matrix.vecMulVec a x i j * JA i k * JB j l * c (Matrix.vecMulVec b x k l) = 0 := by
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun k _ => ?_
  have : ∑ j, ∑ l, Matrix.vecMulVec a x i j * JA i k * JB j l * c (Matrix.vecMulVec b x k l)
      = (a i * JA i k * c (b k)) * ∑ j, ∑ l, x j * JB j l * c (x l) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Matrix.vecMulVec_apply, Matrix.vecMulVec_apply, map_mul]
    ring
  rw [this, hx, mul_zero]

theorem symp_vecMulVec_x_eq_zero : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} (B : Base F E)
    {n d d₁ : ℕ} (W : Spc F E d) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (i₀ i₁ : ℕ) (JX : Matrix (Fin n) (Fin n) E),
    H'.IsAdapted σ B W W₁ i₀ i₁ → ∀ a c : Fin n → AE F E,
    symp (R := AF F) (cA σ) (-1) (incM F JX) (incM F W.J) (Matrix.vecMulVec a (incV F H'.x))
      (Matrix.vecMulVec c (incV F H'.x)) = 0 := by
  intro F E _ _ _ _ _ σ B n d d₁ W W₁ H' i₀ i₁ JX h a c
  have hxx := h.xx
  have hc : ∀ e : E, cA σ (inclR (F := F) (AF F) e) = inclR (F := F) (AF F) (σ e) := by
    intro e
    simp [cA, inclR]
  have hx : ∑ j, ∑ l, incV F H'.x j * incM F W.J j l * cA σ (incV F H'.x l) = 0 := by
    have h2 := congrArg (inclR (F := F) (AF F)) hxx
    rw [map_zero] at h2
    rw [← h2]
    simp only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, Finset.mul_sum, incV, incM,
      Matrix.map_apply, hc, mul_assoc]
  unfold symp hTens
  rw [hTens_vecMulVec_eq_zero (cA σ) _ _ a c _ hx, mul_zero, map_zero]

end GlobalTheory.LagIsotropic
