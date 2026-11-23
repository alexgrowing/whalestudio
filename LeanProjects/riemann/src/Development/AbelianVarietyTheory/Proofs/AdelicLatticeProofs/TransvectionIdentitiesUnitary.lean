import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.IsHermHyperbolic
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1
open NumberField IsDedekindDomain Matrix GlobalTheory.UTrans GlobalTheory.AdLat
open scoped TensorProduct

namespace GlobalTheory.UTrans.Calc

variable {R : Type} [CommRing R] {n : ℕ} (σ : R →+* R) (G : Matrix (Fin n) (Fin n) R)

theorem hf_add_left (x x' y : Fin n → R) : hf σ G (x + x') y = hf σ G x y + hf σ G x' y := by
  simp [hf, add_mul, Finset.sum_add_distrib]

theorem hf_add_right (x y y' : Fin n → R) : hf σ G x (y + y') = hf σ G x y + hf σ G x y' := by
  simp [hf, mul_add, Finset.sum_add_distrib]

theorem hf_smul_left (c : R) (x y : Fin n → R) : hf σ G (c • x) y = c * hf σ G x y := by
  simp [hf, Finset.mul_sum, mul_assoc]

theorem hf_smul_right (c : R) (x y : Fin n → R) : hf σ G x (c • y) = σ c * hf σ G x y := by
  simp only [hf, Finset.mul_sum, Pi.smul_apply, smul_eq_mul, map_mul]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

theorem hf_conj (hσ : ∀ a, σ (σ a) = a) (hG : ∀ a b, σ (G a b) = G b a) (x y : Fin n → R) :
    σ (hf σ G x y) = hf σ G y x := by
  simp only [hf, map_sum, map_mul, hσ, hG]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

theorem tv_mulVec (x : Fin n → R) (t : R) (v : Fin n → R) :
    tv σ G x t *ᵥ v = v + (t * hf σ G v x) • x := by
  rw [tv, Matrix.add_mulVec, Matrix.one_mulVec]
  congr 1
  funext a
  simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, hf, Pi.smul_apply, smul_eq_mul,
    Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun e _ => ?_
  ring

theorem ext_mulVec {A B : Matrix (Fin n) (Fin n) R} (h : ∀ v, A *ᵥ v = B *ᵥ v) : A = B := by
  ext i j
  have := congrFun (h (Pi.single j 1)) i
  simpa using this

theorem tv_mul (x : Fin n → R) (t t' : R) :
    tv σ G x t * tv σ G x t' = tv σ G x (t + t' + t * t' * hf σ G x x) := by
  refine ext_mulVec fun v => ?_
  rw [← Matrix.mulVec_mulVec, tv_mulVec, tv_mulVec, tv_mulVec, hf_add_left, hf_smul_left,
    add_assoc, ← add_smul]
  congr 2
  ring

theorem tv_det (x : Fin n → R) (t : R) : (tv σ G x t).det = 1 + t * hf σ G x x := by
  have h : tv σ G x t = 1 + Matrix.replicateCol Unit (t • x) *
      Matrix.replicateRow Unit (fun b => ∑ e, G b e * σ (x e)) := by
    rw [tv]
    congr 1
    ext a b
    simp [Matrix.mul_apply]
  rw [h, Matrix.det_one_add_replicateCol_mul_replicateRow]
  congr 1
  simp only [dotProduct, hf, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun e _ => ?_
  ring

theorem isU_tv (hσ : ∀ a, σ (σ a) = a) (hG : ∀ a b, σ (G a b) = G b a) (x : Fin n → R) (t : R)
    (h : t + σ t + t * σ t * hf σ G x x = 0) : IsU σ G (tv σ G x t) := by
  intro v w
  rw [tv_mulVec, tv_mulVec]
  simp only [hf_add_left, hf_add_right, hf_smul_left, hf_smul_right, map_mul, hf_conj σ G hσ hG]
  linear_combination (hf σ G v x * hf σ G x w) * h

theorem conj_tv (γ : Matrix (Fin n) (Fin n) R) (x : Fin n → R) (t : R) (h : IsU σ G γ) :
    γ * tv σ G x t = tv σ G (γ *ᵥ x) t * γ := by
  refine ext_mulVec fun v => ?_
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, tv_mulVec, tv_mulVec, h, Matrix.mulVec_add,
    Matrix.mulVec_smul]

theorem tv_smul (a : R) (x : Fin n → R) (t : R) :
    tv σ G (a • x) t = tv σ G x (t * a * σ a) := by
  refine ext_mulVec fun v => ?_
  rw [tv_mulVec, tv_mulVec, hf_smul_right, smul_smul]
  congr 2
  ring

theorem isU_mul (γ γ' : Matrix (Fin n) (Fin n) R) (h : IsU σ G γ) (h' : IsU σ G γ') :
    IsU σ G (γ * γ') := by
  intro v w
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, h, h']

theorem calculus : ∀ (R : Type) [CommRing R] (n : ℕ) (σ : R →+* R) (G : Matrix (Fin n) (Fin n) R), (∀ a, σ (σ a) = a) → (∀ a b, σ (G a b) = G b a) → (∀ x y, σ (hf σ G x y) = hf σ G y x) ∧ (∀ x t v, tv σ G x t *ᵥ v = v + (t * hf σ G v x) • x) ∧ (∀ x t t', tv σ G x t * tv σ G x t' = tv σ G x (t + t' + t * t' * hf σ G x x)) ∧ (∀ x t, (tv σ G x t).det = 1 + t * hf σ G x x) ∧ (∀ x t, t + σ t + t * σ t * hf σ G x x = 0 → IsU σ G (tv σ G x t)) ∧ (∀ γ x t, IsU σ G γ → γ * tv σ G x t = tv σ G (γ *ᵥ x) t * γ) ∧ (∀ (a : R) x t, tv σ G (a • x) t = tv σ G x (t * a * σ a)) ∧ (∀ γ γ', IsU σ G γ → IsU σ G γ' → IsU σ G (γ * γ')) :=
  fun _ _ _ σ G hσ hG => ⟨hf_conj σ G hσ hG, tv_mulVec σ G, tv_mul σ G, tv_det σ G, isU_tv σ G hσ hG,
    conj_tv σ G, tv_smul σ G, isU_mul σ G⟩

end GlobalTheory.UTrans.Calc
