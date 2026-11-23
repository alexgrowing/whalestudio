import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisZero
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.QhtUnip

namespace GlobalTheory.QhtUnip

theorem form_swap_of_skew {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E)
    (hσ : ∀ e, σ (σ e) = e) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (hJ : ∀ i j, σ (J j i) = -J i j)
    (a b : Fin n → E) : σ (form σ J a b) = -form σ J b a := by
  simp only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, hσ, hJ, Finset.mul_sum,
    ← Finset.sum_neg_distrib]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem form_cols {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {n k : ℕ}
    (J : Matrix (Fin n) (Fin n) E) (ι : Matrix (Fin n) (Fin k) E) (a b : Fin k) :
    form σ J (fun r => ι r a) (fun r => ι r b) = (ιᵀ * J * ι.map σ) a b := by
  simp only [form, dotProduct, Matrix.mulVec, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
    Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem form_adaptedBasis_eq_gram : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), (∀ e, σ (σ e) = e) → ∀ (B : Base F E) {m : ℕ} (W : Spc F E (m + 2)) (r s : ℕ), W.IsSkew σ B r s →
    ∀ (W₁ : Spc F E m) (H : Plane E (m + 2) m) (i₀ i₁ : ℕ), H.IsAdapted σ B W W₁ i₀ i₁ → ∀ i j : Ix m, form σ W.J (fun r => basP H r i) (fun r => basP H r j) = gI W₁.J i j := by
  intro F E _ _ _ _ _ σ hσ B m W r s hW W₁ H i₀ i₁ hA i j
  have sw := form_swap_of_skew σ hσ W.J hW.skew
  have hcol : ∀ k, (fun r => H.ι r k) = H.ι *ᵥ Pi.single k 1 := by
    intro k; ext r; simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  have ιx : ∀ k, form σ W.J (fun r => H.ι r k) H.x = 0 := fun k => by rw [hcol]; exact (hA.orth _).1
  have ιy : ∀ k, form σ W.J (fun r => H.ι r k) H.y = 0 := fun k => by rw [hcol]; exact (hA.orth _).2
  have xι : ∀ k, form σ W.J H.x (fun r => H.ι r k) = 0 := fun k => by
    have := sw (fun r => H.ι r k) H.x; rw [ιx, map_zero] at this; exact neg_eq_zero.mp this.symm
  have yι : ∀ k, form σ W.J H.y (fun r => H.ι r k) = 0 := fun k => by
    have := sw (fun r => H.ι r k) H.y; rw [ιy, map_zero] at this; exact neg_eq_zero.mp this.symm
  have yx : form σ W.J H.y H.x = -1 := by
    have := sw H.x H.y; rw [hA.xy, map_one] at this; exact (neg_eq_iff_eq_neg.mp this.symm).symm ▸ by ring
  have ιι : ∀ a b, form σ W.J (fun r => H.ι r a) (fun r => H.ι r b) = W₁.J a b := fun a b => by
    rw [form_cols, hA.gram]
  rcases i with ((i | i) | i) <;> rcases j with ((j | j) | j) <;>
    simp [basP, gI, Matrix.fromBlocks, hA.xx, hA.yy, hA.xy, yx, ιx, ιy, xι, yι, ιι]

end GlobalTheory.QhtUnip
