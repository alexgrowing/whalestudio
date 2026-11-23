import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NmatMulVec
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.UnipMass

noncomputable section
namespace GlobalTheory.UnipMass
namespace ProdFormula
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem cA_cA_of_invol (σ : E →ₐ[F] E) (hσ : ∀ a, σ (σ a) = a) (z : AE F E) : cA σ (cA σ z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [cA, hσ]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem cA_incM_apply (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (i j : Fin n) :
    cA σ (incM F J i j) = incM F (J.map σ) i j := by
  simp [cA, incM, inclR]

theorem hA_swap (σ : E →ₐ[F] E) (hσ : ∀ a, σ (σ a) = a) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (hJ : ∀ i j, σ (J j i) = -J i j) (v w : Fin n → AE F E) : hA σ J w v = - cA σ (hA σ J v w) := by
  simp only [hA, dotProduct, Matrix.mulVec, map_sum, map_mul, cA_cA_of_invol σ hσ, cA_incM_apply]
  simp only [incM, Matrix.map_apply, hJ, map_neg]
  simp only [Finset.mul_sum, neg_mul, mul_neg, Finset.sum_neg_distrib, neg_neg]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem hA_add_left (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (v v' w : Fin n → AE F E) :
    hA σ J (v + v') w = hA σ J v w + hA σ J v' w := by
  simp only [hA, add_dotProduct]

theorem hA_sub_left (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (v v' w : Fin n → AE F E) :
    hA σ J (v - v') w = hA σ J v w - hA σ J v' w := by
  simp only [hA, sub_dotProduct]

theorem hA_smul_left (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (a : AE F E) (v w : Fin n → AE F E) :
    hA σ J (a • v) w = a * hA σ J v w := by
  simp only [hA, smul_dotProduct, smul_eq_mul]

theorem hA_add_right (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (v w w' : Fin n → AE F E) :
    hA σ J v (w + w') = hA σ J v w + hA σ J v w' := by
  have : (fun i => cA σ ((w + w') i)) = (fun i => cA σ (w i)) + fun i => cA σ (w' i) := by
    funext i; simp
  simp only [hA, this, Matrix.mulVec_add, dotProduct_add]

end ProdFormula

open ProdFormula in

theorem nmat_mul_nmat : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), (∀ a, σ (σ a) = a) → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), (∀ i j, σ (J j i) = -J i j) →
    ∀ (x u u' : Fin n → AE F E) (c c' : AE F E), hA σ J x x = 0 → hA σ J u x = 0 → hA σ J u' x = 0 →
    nmat σ J x u c * nmat σ J x u' c' = nmat σ J x (u + u') (c + c' - hA σ J u' u) := by
  intro F E _ _ _ _ _ σ hσ n J hJ x u u' c c' hxx hux hu'x
  have hxu : hA σ J x u = 0 := by rw [hA_swap σ hσ J hJ u x, hux, map_zero, neg_zero]
  have key : ∀ v, (nmat σ J x u c * nmat σ J x u' c') *ᵥ v =
      nmat σ J x (u + u') (c + c' - hA σ J u' u) *ᵥ v := by
    intro v
    rw [← Matrix.mulVec_mulVec, nmat_mulVec, nmat_mulVec, nmat_mulVec]
    simp only [hA_add_left, hA_sub_left, hA_smul_left, hA_add_right, hxx, hux, hu'x, hxu]
    ext i
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  exact Matrix.toLin'.injective (LinearMap.ext fun v => by simpa only [Matrix.toLin'_apply] using key v)

end GlobalTheory.UnipMass
