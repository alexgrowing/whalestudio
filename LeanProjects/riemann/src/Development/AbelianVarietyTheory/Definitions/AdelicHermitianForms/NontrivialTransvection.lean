import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.IsHermHyperbolic

noncomputable section
namespace GlobalTheory.UTrans.Model
open GlobalTheory.UTrans
variable {R : Type} [CommRing R] {n : ℕ}

theorem tv_mulVec (σ : R →+* R) (G : Matrix (Fin n) (Fin n) R) (x v : Fin n → R) (t : R) :
    (tv σ G x t).mulVec v = v + (t * hf σ G v x) • x := by
  rw [tv, Matrix.add_mulVec, Matrix.one_mulVec]
  ext a
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct, Matrix.of_apply, hf,
    Finset.mul_sum, Finset.sum_mul]
  congr 1
  exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun e _ => by ring

theorem hf_add_smul_left (σ : R →+* R) (G : Matrix (Fin n) (Fin n) R) (v x y : Fin n → R) (c : R) :
    hf σ G (v + c • x) y = hf σ G v y + c * hf σ G x y := by
  simp only [hf, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul, Finset.sum_add_distrib, Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

theorem hf_add_smul_right (σ : R →+* R) (G : Matrix (Fin n) (Fin n) R) (v x y : Fin n → R) (c : R) :
    hf σ G y (v + c • x) = hf σ G y v + σ c * hf σ G y x := by
  simp only [hf, Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add, map_mul, mul_add,
    Finset.sum_add_distrib, Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

theorem hf_conj (σ : R →+* R) (G : Matrix (Fin n) (Fin n) R) (hσ : ∀ a, σ (σ a) = a)
    (hG : ∀ a b, σ (G a b) = G b a) (x y : Fin n → R) : σ (hf σ G x y) = hf σ G y x := by
  simp only [hf, map_sum, map_mul, hσ, hG]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

theorem isU_tv (σ : R →+* R) (G : Matrix (Fin n) (Fin n) R) (hσ : ∀ a, σ (σ a) = a)
    (hG : ∀ a b, σ (G a b) = G b a) (x : Fin n → R) (t : R)
    (h : t + σ t + t * σ t * hf σ G x x = 0) : IsU σ G (tv σ G x t) := by
  intro v w
  rw [tv_mulVec, tv_mulVec, hf_add_smul_left, hf_add_smul_right, hf_add_smul_right, map_mul,
    hf_conj σ G hσ hG w x]
  linear_combination (hf σ G v x * hf σ G x w) * h

theorem isU_of_mem_tvGen (σ : R →+* R) (G : Matrix (Fin n) (Fin n) R) (hσ : ∀ a, σ (σ a) = a)
    (hG : ∀ a b, σ (G a b) = G b a) {m} (hm : m ∈ TvGen σ G) : IsU σ G m := by
  induction hm using Submonoid.closure_induction with
  | mem m hm =>
    obtain ⟨x, t, hx, ht, rfl⟩ := hm
    exact isU_tv σ G hσ hG x t (by rw [hx, mul_zero, add_zero]; exact ht)
  | one => intro v w; simp only [Matrix.one_mulVec]
  | mul p q _ _ hp hq =>
    intro v w
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hp, hq]

theorem det_tv (σ : R →+* R) (G : Matrix (Fin n) (Fin n) R) (x : Fin n → R) (t : R) :
    (tv σ G x t).det = 1 + t * hf σ G x x := by
  have e : tv σ G x t = (1 : Matrix (Fin n) (Fin n) R) + Matrix.replicateCol (Fin 1) x *
      Matrix.replicateRow (Fin 1) (fun b : Fin n => t * ∑ e : Fin n, G b e * σ (x e)) := by
    unfold tv
    congr 1
    ext a b
    simp [Matrix.mul_apply, Matrix.replicateCol_apply, Matrix.replicateRow_apply]
    ring
  rw [e]
  refine (Matrix.det_one_add_replicateCol_mul_replicateRow (ι := Fin 1) x _).trans ?_
  simp only [dotProduct, hf, Finset.mul_sum, Finset.sum_mul]
  congr 1
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

theorem det_of_mem_tvGen (σ : R →+* R) (G : Matrix (Fin n) (Fin n) R) {m} (hm : m ∈ TvGen σ G) : m.det = 1 := by
  induction hm using Submonoid.closure_induction with
  | mem m hm =>
    obtain ⟨x, t, hx, _, rfl⟩ := hm
    rw [det_tv, hx, mul_zero, add_zero]
  | one => exact Matrix.det_one
  | mul p q _ _ hp hq => rw [Matrix.det_mul, hp, hq, mul_one]

theorem nontrivial_transvection :
    !![1, Complex.I; 0, 1] ∈ TvGen (starRingEnd ℂ) !![0, 1; 1, 0] := by
  apply Submonoid.subset_closure
  refine ⟨![1, 0], Complex.I, ?_, ?_, ?_⟩
  · simp [hf, Fin.sum_univ_two]
  · simp [Complex.conj_I]
  · ext a b
    fin_cases a <;> fin_cases b <;> simp [tv, Fin.sum_univ_two]

theorem not_mem_tvGen :
    IsU (starRingEnd ℂ) !![0, 1; 1, 0] !![Complex.I, 0; 0, Complex.I] ∧
    !![Complex.I, 0; 0, Complex.I] ∉ TvGen (starRingEnd ℂ) !![0, 1; 1, 0] := by
  have hI : ∀ v : Fin 2 → ℂ, (!![Complex.I, 0; 0, Complex.I]).mulVec v = Complex.I • v := by
    intro v
    ext i
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  refine ⟨fun v w => ?_, fun hm => ?_⟩
  · simp only [hf, hI, Pi.smul_apply, smul_eq_mul, map_mul, Complex.conj_I]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    linear_combination (-(v a * !![(0 : ℂ), 1; 1, 0] a b * (starRingEnd ℂ) (w b))) * Complex.I_sq
  · have hd := det_of_mem_tvGen _ _ hm
    rw [Matrix.det_fin_two_of] at hd
    norm_num [Complex.ext_iff] at hd

theorem not_isU : ¬ IsU (starRingEnd ℂ) !![0, 1; 1, 0] !![1, 1; 0, 1] := by
  intro h
  have h1 := h ![0, 1] ![0, 1]
  norm_num [hf, Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h1

end GlobalTheory.UTrans.Model
