import Mathlib
import Formalism.LocalToGlobal.HermitianForms.IsLocBasis
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolFunApply

noncomputable section

namespace GlobalTheory.IntegralityCompare

open MvPolynomial Formalism.L2.Forms

theorem fnOf_apply_eq {ι : Type} [Fintype ι] {n : ℕ} (G : ι → Matrix (Fin n) (Fin n) ℂ) (s : ι → ℤ)
    (A : ι → Matrix (Fin n) (Fin n) ℂ) (P : MvPolynomial (ι × Fin n × Fin n) ℂ) (y : Frames G) :
    fnOf G s A P y = (∏ τ, (A τ * y.1 τ).det ^ s τ) *
      eval (fun x : ι × Fin n × Fin n => (A x.1 * y.1 x.1) x.2.1 x.2.2) P := rfl

theorem map_mul_map_inv {E ι : Type} [Field E] {n : ℕ} (emb : ι → E →+* ℂ) (M : GL (Fin n) E) (τ : ι) :
    (M : Matrix (Fin n) (Fin n) E).map (emb τ) *
      ((M⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E).map (emb τ) = 1 := by
  rw [← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]

theorem map_inv_mul_map {E ι : Type} [Field E] {n : ℕ} (emb : ι → E →+* ℂ) (M : GL (Fin n) E) (τ : ι) :
    ((M⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E).map (emb τ) *
      (M : Matrix (Fin n) (Fin n) E).map (emb τ) = 1 := by
  rw [← Matrix.map_mul, Units.inv_mul, Matrix.map_one _ (map_zero _) (map_one _)]

theorem det_map_emb {E ι : Type} [Field E] {n : ℕ} (emb : ι → E →+* ℂ) (M : Matrix (Fin n) (Fin n) E) (τ : ι) :
    emb τ M.det = (M.map (emb τ)).det := RingHom.map_det _ _

theorem fnOf_inv_twSub {E ι : Type} [Field E] [Fintype ι] {n : ℕ} (emb : ι → E →+* ℂ) (M : GL (Fin n) E)
    (s : ι → ℤ) (G : ι → Matrix (Fin n) (Fin n) ℂ) (P0 : MvPolynomial (ι × Fin n × Fin n) ℂ) (y : Frames G) :
    fnOf G s (atInf emb ((M⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E)) (twSub emb M s P0) y
      = fnOf G s 1 P0 y := by
  rw [fnOf_apply_eq, fnOf_apply_eq]
  have h := eval_twSub emb M s P0
    (fun τ => atInf emb ((M⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) τ * y.1 τ)
  have hy : ∀ τ, (M : Matrix (Fin n) (Fin n) E).map (emb τ) *
      (atInf emb ((M⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) τ * y.1 τ) = y.1 τ := by
    intro τ; rw [← Matrix.mul_assoc, atInf, map_mul_map_inv, Matrix.one_mul]
  simp only [hy] at h
  rw [h]
  simp only [Pi.one_apply, Matrix.one_mul]
  rw [← mul_assoc, ← Finset.prod_mul_distrib]
  congr 1
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [mul_comm, ← mul_zpow, det_map_emb, ← Matrix.det_mul, hy]

theorem exists_det_poly {ι : Type} [Fintype ι] {n : ℕ} :
    ∃ D : MvPolynomial (ι × Fin n × Fin n) ℂ, ∀ x : ι → Matrix (Fin n) (Fin n) ℂ,
      eval (fun k : ι × Fin n × Fin n => x k.1 k.2.1 k.2.2) D = ∏ τ, (x τ).det := by
  refine ⟨∏ τ, Matrix.det (Matrix.of fun a b => (X (τ, a, b) : MvPolynomial (ι × Fin n × Fin n) ℂ)), ?_⟩
  intro x
  rw [map_prod]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [RingHom.map_det]
  congr 1
  ext a b
  simp

theorem eq_of_eval_units {ι : Type} [Fintype ι] {n : ℕ} (Q : MvPolynomial (ι × Fin n × Fin n) ℂ)
    (hQ : ∀ x : ι → Matrix (Fin n) (Fin n) ℂ, (∀ τ, IsUnit (x τ).det) →
      eval (fun k : ι × Fin n × Fin n => x k.1 k.2.1 k.2.2) Q = 0) : Q = 0 := by
  obtain ⟨D, hD⟩ := exists_det_poly (ι := ι) (n := n)
  have hQD : Q * D = 0 := by
    apply MvPolynomial.funext
    intro x
    let xm : ι → Matrix (Fin n) (Fin n) ℂ := fun τ a b => x (τ, a, b)
    rw [map_zero, map_mul]
    show eval (fun k : ι × Fin n × Fin n => xm k.1 k.2.1 k.2.2) Q *
      eval (fun k : ι × Fin n × Fin n => xm k.1 k.2.1 k.2.2) D = 0
    rw [hD]
    by_cases hu : ∀ τ, IsUnit (xm τ).det
    · rw [hQ _ hu, zero_mul]
    · push_neg at hu
      obtain ⟨τ, hτ⟩ := hu
      rw [isUnit_iff_ne_zero, not_not] at hτ
      rw [Finset.prod_eq_zero (Finset.mem_univ τ) hτ, mul_zero]
  have hD0 : D ≠ 0 := by
    intro h0
    have := hD (fun _ => 1)
    rw [h0, map_zero] at this
    simp at this
  exact (mul_eq_zero.mp hQD).resolve_right hD0

theorem fnOf_inv_iff_twSub_mem : ∀ {E ι : Type} [Field E] [Fintype ι] {n : ℕ} (emb : ι → E →+* ℂ) (M : GL (Fin n) E) (s : ι → ℤ)
    (G : ι → Matrix (Fin n) (Fin n) ℂ) (P0 : MvPolynomial (ι × Fin n × Fin n) ℂ)
    (S : AddSubgroup (MvPolynomial (ι × Fin n × Fin n) ℂ)) {Yt : Type} (e : Yt ≃ Frames G) (f : Yt → ℂ),
    (∀ z, f z = fnOf G s 1 P0 (e z)) →
    ((∃ P ∈ S, ∀ z, f z = fnOf G s (atInf emb ((M⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E)) P (e z)) ↔
      twSub emb M s P0 ∈ S) := by
  intro E ι _ _ n emb M s G P0 S Yt e f hf
  constructor
  · rintro ⟨P, hP, hPf⟩
    have hall : ∀ y : Frames G,
        fnOf G s (atInf emb ((M⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E)) P y =
        fnOf G s (atInf emb ((M⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E)) (twSub emb M s P0) y := by
      intro y
      obtain ⟨z, rfl⟩ := e.surjective y
      rw [← hPf, hf, fnOf_inv_twSub]
    suffices hPeq : P - twSub emb M s P0 = 0 by
      rw [sub_eq_zero] at hPeq
      rw [← hPeq]; exact hP
    apply eq_of_eval_units
    intro x hx
    have hMu : IsUnit (M : Matrix (Fin n) (Fin n) E).det :=
      (Matrix.isUnit_iff_isUnit_det _).mp M.isUnit
    let y : Frames G := ⟨fun τ => (M : Matrix (Fin n) (Fin n) E).map (emb τ) * x τ, fun τ => by
      rw [Matrix.det_mul, ← det_map_emb]; exact (hMu.map (emb τ)).mul (hx τ)⟩
    have h1 := hall y
    rw [fnOf_apply_eq, fnOf_apply_eq] at h1
    have hAx : ∀ τ, atInf emb ((M⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) τ * y.1 τ = x τ := by
      intro τ
      show atInf emb ((M⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) τ *
        ((M : Matrix (Fin n) (Fin n) E).map (emb τ) * x τ) = x τ
      rw [← Matrix.mul_assoc, atInf, map_inv_mul_map, Matrix.one_mul]
    simp only [hAx] at h1
    have hne : (∏ τ, (x τ).det ^ s τ) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun τ _ => zpow_ne_zero _ (hx τ).ne_zero
    rw [map_sub, sub_eq_zero]
    exact mul_left_cancel₀ hne h1
  · intro h
    exact ⟨_, h, fun z => by rw [hf, fnOf_inv_twSub]⟩

end GlobalTheory.IntegralityCompare
