import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TrPApply
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ArchSch

noncomputable section

namespace GlobalTheory.ArchSch

theorem form_swap_of_skew {F E : Type} [Field F] [Field E] [Algebra F E] {σ : E →ₐ[F] E} {d : ℕ}
    (J : Matrix (Fin d) (Fin d) E) (hσ : ∀ x, σ (σ x) = x) (hJ : ∀ i j, σ (J j i) = -J i j) (x y : Fin d → E) :
    form σ J y x = -σ (form σ J x y) := by
  simp only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, hσ, hJ, Finset.mul_sum, ← Finset.sum_neg_distrib]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem symp_dual_iso : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    (B : Base F E) {n d d₁ : ℕ} (W : Spc F E d) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (r' s' i₀ i₁ : ℕ)
    (JX : Matrix (Fin n) (Fin n) E),
    W.IsSkew σ B r' s' → H'.IsAdapted σ B W W₁ i₀ i₁ → ∀ (_hB : B.IsGood σ := by assumption) (b c : Fin n → AE F E),
    symp (R := AF F) (cA σ) (-1) (incM F JX) (incM F W.J) (Matrix.vecMulVec b (incV F H'.y))
      (Matrix.vecMulVec c (incV F H'.x)) =
    Algebra.trace (AF F) (AE F E) (b ⬝ᵥ (incM F JX *ᵥ fun k => cA σ (c k))) := by
  intro F E _ _ _ _ _ σ B n d d₁ W W₁ H' r' s' i₀ i₁ JX hW hH hB b c
  have hσ : ∀ x, σ (σ x) = x := fun x => by
    obtain ⟨-, -, -, h⟩ := hB.cm
    let τ : E →+* ℂ := Classical.choice (inferInstance : Nonempty (E →+* ℂ))
    apply τ.injective
    rw [h τ, h τ, star_star]
  have hyx : form σ W.J H'.y H'.x = -1 := by
    rw [form_swap_of_skew W.J hσ hW.skew, hH.xy, map_one]
  have hc : ∀ e : E, cA σ (inclR (F := F) (AF F) e) = inclR (F := F) (AF F) (σ e) := fun e => rfl
  have h1 : ∑ j, ∑ l, inclR (F := F) (AF F) (H'.y j) * inclR (F := F) (AF F) (W.J j l) *
      inclR (F := F) (AF F) (σ (H'.x l)) = -1 := by
    have := congrArg (inclR (F := F) (AF F)) hyx
    simp only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, Finset.mul_sum, map_neg, map_one] at this
    simpa only [mul_assoc] using this
  unfold symp hTens
  congr 1
  have h2 : ∀ i, ∑ j, ∑ k, ∑ l, Matrix.vecMulVec b (incV F H'.y) i j * incM F JX i k * incM F W.J j l *
      cA σ (Matrix.vecMulVec c (incV F H'.x) k l) = -∑ k, b i * (incM F JX i k * cA σ (c k)) := by
    intro i
    rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← mul_neg_one, ← h1, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    simp only [Matrix.vecMulVec_apply, map_mul, incV, hc, incM, Matrix.map_apply]
    ring
  simp only [h2, dotProduct, Matrix.mulVec, Finset.mul_sum, Finset.sum_neg_distrib, neg_mul, one_mul, neg_neg]

end GlobalTheory.ArchSch
