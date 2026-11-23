import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitHomVal
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace GlobalTheory.SplitCoord.GramAt

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem prod_apply (σ : E →ₐ[F] E) {n : ℕ} {κ : Type} [Fintype κ] (J : Matrix (Fin n) (Fin n) E)
    (M : Matrix (Fin n) κ E) (p q : κ) :
    (Mᵀ * J * M.map σ) p q = form σ J (fun r => M r p) (fun r => M r q) := by
  rw [Matrix.mul_assoc]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, form, dotProduct, Matrix.mulVec]

theorem form_swap (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (hJ : ∀ i j, σ (J j i) = -J i j) (x y : Fin n → E) :
    form σ J y x = -σ (form σ J x y) := by
  have hJ' : ∀ r s, J s r = -σ (J r s) := fun r s => by rw [hJ s r, neg_neg]
  simp only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, hσ, Finset.mul_sum, ← Finset.sum_neg_distrib]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun s _ => ?_
  rw [hJ' r s]; ring

theorem col_mid {n m : ℕ} (ι : Matrix (Fin n) (Fin m) E) (j : Fin m) :
    (fun r => ι r j) = ι *ᵥ Pi.single j 1 := by
  funext r; simp [Matrix.mulVec, dotProduct, Pi.single_apply]

variable {σ : E →ₐ[F] E} (hσ : ∀ x, σ (σ x) = x) {B : Base F E} {n m : ℕ} {W : Spc F E n} {W₁ : Spc F E m}
  {H : Plane E n m} {i₀ i₁ : ℕ} (hH : H.IsAdapted σ B W W₁ i₀ i₁) (hJ : ∀ i j, σ (W.J j i) = -W.J i j)
include hH

theorem gram_middle_x_eq_zero (j : Fin m) : form σ W.J (fun r => H.ι r j) H.x = 0 := by
  rw [col_mid]; exact (hH.orth _).1

theorem mid_y (j : Fin m) : form σ W.J (fun r => H.ι r j) H.y = 0 := by
  rw [col_mid]; exact (hH.orth _).2

theorem mid_mid (i j : Fin m) : form σ W.J (fun r => H.ι r i) (fun r => H.ι r j) = W₁.J i j := by
  rw [← prod_apply σ W.J H.ι i j, hH.gram]

include hσ hJ

theorem x_mid (j : Fin m) : form σ W.J H.x (fun r => H.ι r j) = 0 := by
  rw [form_swap σ hσ W.J hJ, gram_middle_x_eq_zero hH j, map_zero, neg_zero]

theorem y_mid (j : Fin m) : form σ W.J H.y (fun r => H.ι r j) = 0 := by
  rw [form_swap σ hσ W.J hJ, mid_y hH j, map_zero, neg_zero]

theorem y_x : form σ W.J H.y H.x = -1 := by
  rw [form_swap σ hσ W.J hJ, hH.xy, map_one]

theorem form_colS : ∀ a b : Ix m, form σ W.J (colS H.x H.y H.ι a) (colS H.x H.y H.ι b) = gamS W₁.J a b
  | ⟨0, _⟩, ⟨0, _⟩ => hH.xx
  | ⟨0, _⟩, ⟨1, j⟩ => x_mid hσ hH hJ (m := m) j
  | ⟨0, _⟩, ⟨2, _⟩ => hH.xy
  | ⟨1, i⟩, ⟨0, _⟩ => gram_middle_x_eq_zero hH (m := m) i
  | ⟨1, i⟩, ⟨1, j⟩ => mid_mid hH (m := m) i j
  | ⟨1, i⟩, ⟨2, _⟩ => mid_y hH (m := m) i
  | ⟨2, _⟩, ⟨0, _⟩ => y_x hσ hH hJ
  | ⟨2, _⟩, ⟨1, j⟩ => y_mid hσ hH hJ (m := m) j
  | ⟨2, _⟩, ⟨2, _⟩ => hH.yy

omit hσ hH hJ in
theorem gamS_map {R S : Type} [Ring R] [Ring S] (f : R →+* S) {m : ℕ} (K : Matrix (Fin m) (Fin m) R) :
    ∀ a b : Ix m, gamS (K.map f) a b = f (gamS K a b)
  | ⟨0, _⟩, ⟨0, _⟩ => (map_zero f).symm
  | ⟨0, _⟩, ⟨1, _⟩ => (map_zero f).symm
  | ⟨0, _⟩, ⟨2, _⟩ => (map_one f).symm
  | ⟨1, _⟩, ⟨0, _⟩ => (map_zero f).symm
  | ⟨1, _⟩, ⟨1, _⟩ => rfl
  | ⟨1, _⟩, ⟨2, _⟩ => (map_zero f).symm
  | ⟨2, _⟩, ⟨0, _⟩ => by show -1 = f (-1); rw [map_neg, map_one]
  | ⟨2, _⟩, ⟨1, _⟩ => (map_zero f).symm
  | ⟨2, _⟩, ⟨2, _⟩ => (map_zero f).symm

omit hσ hH hJ in
theorem gam_map {R S : Type} [Ring R] [Ring S] (f : R →+* S) {m n : ℕ} (e : Ix m ≃ Fin n)
    (K : Matrix (Fin m) (Fin m) R) : gam e (K.map f) = (gam e K).map f := by
  ext p q
  exact gamS_map f K (e.symm p) (e.symm q)

theorem basMat_gram_E (e : Ix m ≃ Fin n) : (basMat H e)ᵀ * W.J * (basMat H e).map σ = gam e W₁.J := by
  ext p q
  rw [prod_apply]
  exact form_colS hσ hH hJ (e.symm p) (e.symm q)

end GlobalTheory.SplitCoord.GramAt

namespace GlobalTheory.SplitCoord

open GramAt in

theorem basMat_gram : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (n m : ℕ) (W : Spc F E n) (W₁ : Spc F E m) (H : Plane E n m) (i₀ i₁ : ℕ),
    (∀ x, σ (σ x) = x) → H.IsAdapted σ B W W₁ i₀ i₁ →
    (∀ i j, σ (W.J j i) = -W.J i j) → ∀ (v : Pl F) (t : E →ₐ[F] Fv F v) (e : GlobalTheory.SplitCoord.Ix m ≃ Fin n),
    ((GlobalTheory.SplitCoord.basMat H e).map t)ᵀ * W.J.map t * (GlobalTheory.SplitCoord.basMat H e).map (t.comp σ) =
      GlobalTheory.SplitCoord.gam e (W₁.J.map t) := by
  intro F E _ _ _ _ _ σ B n m W W₁ H i₀ i₁ hσ hH hJ v t e
  have h1 : ((basMat H e).map t)ᵀ * W.J.map t * (basMat H e).map (t.comp σ) =
      ((basMat H e)ᵀ * W.J * (basMat H e).map σ).map t := by
    ext r s
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, map_sum, map_mul, AlgHom.comp_apply]
  rw [h1, basMat_gram_E hσ hH hJ e]
  exact (gam_map (t : E →+* Fv F v) e W₁.J).symm

end GlobalTheory.SplitCoord
