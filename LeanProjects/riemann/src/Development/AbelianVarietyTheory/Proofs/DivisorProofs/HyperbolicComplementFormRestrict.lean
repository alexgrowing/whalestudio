import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHaarOfIsCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatHomOfGAdSymm
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.LeviIndep

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem form_swap (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (hσ : ∀ z, σ (σ z) = z) (hJ : ∀ i j, σ (J j i) = J i j) (u v : Fin n → E) :
    σ (form σ J u v) = form σ J v u := by
  simp only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, hσ, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hJ i j]; ring

theorem incV_pair (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (v z : Fin n → E) :
    incV F v ⬝ᵥ (fun i => inclR (F := F) (AF F) ((J *ᵥ fun j => σ (z j)) i)) =
      inclR (F := F) (AF F) (form σ J v z) := by
  simp only [incV, form, dotProduct, map_sum, map_mul]

theorem incM_pair (σ : E →ₐ[F] E) {n n₁ : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (ι : Matrix (Fin n) (Fin n₁) E) (w : Fin n₁ → AE F E) (z : Fin n → E) :
    (incM F ι *ᵥ w) ⬝ᵥ (fun i => inclR (F := F) (AF F) ((J *ᵥ fun j => σ (z j)) i)) =
      ∑ k : Fin n₁, (w k * inclR (F := F) (AF F) (form σ J (fun i => ι i k) z) : AE F E) := by
  simp only [incM, form, dotProduct, Matrix.mulVec, Matrix.map_apply, map_sum, map_mul,
    Finset.sum_mul, Finset.mul_sum]
  conv_lhs => arg 2; ext i; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

end GlobalTheory.LeviIndep

namespace GlobalTheory.LeviIndep

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem gram_apply (σ : E →ₐ[F] E) {n n₁ : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (ι : Matrix (Fin n) (Fin n₁) E) (k l : Fin n₁) :
    (ιᵀ * J * ι.map σ) k l = form σ J (fun i => ι i k) (fun i => ι i l) := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, form, dotProduct,
    Matrix.mulVec, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem relation_pair (σ : E →ₐ[F] E) {n n₁ : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (x y : Fin n → E) (ι : Matrix (Fin n) (Fin n₁) E) (a b : AE F E) (w : Fin n₁ → AE F E)
    (h : a • incV F x + incM F ι *ᵥ w + b • incV F y = 0) (z : Fin n → E) :
    a * inclR (F := F) (AF F) (form σ J x z) +
      ∑ k : Fin n₁, (w k * inclR (F := F) (AF F) (form σ J (fun i => ι i k) z) : AE F E) +
      b * inclR (F := F) (AF F) (form σ J y z) = 0 := by
  have h' := congrArg (fun u => u ⬝ᵥ (fun i => inclR (F := F) (AF F) ((J *ᵥ fun j => σ (z j)) i))) h
  simp only [add_dotProduct, smul_dotProduct, smul_eq_mul, zero_dotProduct] at h'
  rwa [incV_pair, incV_pair, incM_pair] at h'

theorem col_eq {n n₁ : ℕ} (ι : Matrix (Fin n) (Fin n₁) E) (k : Fin n₁) :
    ι *ᵥ Pi.single k 1 = fun i => ι i k := by
  ext i; simp [Matrix.mulVec, dotProduct, Pi.single_apply]

theorem indep : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n n₁ : ℕ)
    (J : Matrix (Fin n) (Fin n) E) (J₁ : Matrix (Fin n₁) (Fin n₁) E) (x y : Fin n → E) (ι : Matrix (Fin n) (Fin n₁) E),
    (∀ z, σ (σ z) = z) → (∀ i j, σ (J j i) = J i j) → form σ J x x = 0 → form σ J y y = 0 →
    form σ J x y = 1 → (∀ u, form σ J (ι *ᵥ u) x = 0 ∧ form σ J (ι *ᵥ u) y = 0) → ιᵀ * J * ι.map σ = J₁ → J₁.det ≠ 0 →
    ∀ (a b : AE F E) (w : Fin n₁ → AE F E), a • incV F x + incM F ι *ᵥ w + b • incV F y = 0 → a = 0 ∧ w = 0 ∧ b = 0 := by
  intro F E _ _ _ _ _ σ n n₁ J J₁ x y ι hσ hJ hxx hyy hxy hι hJ₁ hdet a b w h
  have hcx : ∀ k : Fin n₁, form σ J (fun i => ι i k) x = 0 := fun k => by
    rw [← col_eq]; exact (hι _).1
  have hcy : ∀ k : Fin n₁, form σ J (fun i => ι i k) y = 0 := fun k => by
    rw [← col_eq]; exact (hι _).2
  have hyx : form σ J y x = 1 := by rw [← form_swap σ J hσ hJ x y, hxy, map_one]
  have hxc : ∀ l : Fin n₁, form σ J x (fun i => ι i l) = 0 := fun l => by
    rw [← form_swap σ J hσ hJ, hcx, map_zero]
  have hyc : ∀ l : Fin n₁, form σ J y (fun i => ι i l) = 0 := fun l => by
    rw [← form_swap σ J hσ hJ, hcy, map_zero]
  have ha : a = 0 := by
    have := relation_pair σ J x y ι a b w h y
    simpa [hxy, hcy, hyy] using this
  have hb : b = 0 := by
    have := relation_pair σ J x y ι a b w h x
    simpa [hxx, hcx, hyx] using this
  refine ⟨ha, ?_, hb⟩
  set A : Matrix (Fin n₁) (Fin n₁) (AE F E) := incM F J₁ with hA
  have hv : w ᵥ* A = 0 := by
    ext l
    have := relation_pair σ J x y ι a b w h (fun i => ι i l)
    simp only [hxc, hyc, map_zero, mul_zero, zero_add, add_zero] at this
    simp only [Matrix.vecMul, dotProduct, hA, incM, Matrix.map_apply, Pi.zero_apply, ← hJ₁,
      gram_apply]
    exact this
  have hu : IsUnit A.det := by
    have : A.det = inclR (F := F) (AF F) J₁.det := by
      rw [RingHom.map_det]; rfl
    rw [this]; exact (isUnit_iff_ne_zero.mpr hdet).map _
  calc w = w ᵥ* (A * A⁻¹) := by rw [Matrix.mul_nonsing_inv A hu, Matrix.vecMul_one]
    _ = 0 := by rw [← Matrix.vecMul_vecMul, hv, Matrix.zero_vecMul]

end GlobalTheory.LeviIndep
