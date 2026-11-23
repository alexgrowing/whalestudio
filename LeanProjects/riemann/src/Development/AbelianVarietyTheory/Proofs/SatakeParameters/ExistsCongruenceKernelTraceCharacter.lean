import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.PolyApproxZeroPadic
open GlobalTheory.Cong

namespace GlobalTheory.CongChar

variable {R : Type} [CommRing R] [IsDomain R] {a : ℕ} {c : R}

theorem exists_eq_one_add_smul
    (g : (Matrix.GeneralLinearGroup.map (n := Fin a) (Ideal.Quotient.mk (Ideal.span {c}))).ker) :
    ∃ x : Matrix (Fin a) (Fin a) R, (g.1 : Matrix (Fin a) (Fin a) R) = 1 + c • x := by
  have hg := g.2
  rw [MonoidHom.mem_ker] at hg
  have h : ∀ i j, (g.1 : Matrix (Fin a) (Fin a) R) i j - (1 : Matrix (Fin a) (Fin a) R) i j
      ∈ Ideal.span {c} := by
    intro i j
    rw [← Ideal.Quotient.eq]
    have := congrArg (fun M : GL (Fin a) (R ⧸ Ideal.span {c}) => M.1 i j) hg
    simp only [Matrix.GeneralLinearGroup.map_apply, Units.val_one] at this
    rw [this]
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  choose x hx using fun i j => Ideal.mem_span_singleton'.1 (h i j)
  refine ⟨Matrix.of x, ?_⟩
  ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.of_apply]
  linear_combination (-1 : R) * hx i j

theorem smul_injective (hc : c ≠ 0) {x y : Matrix (Fin a) (Fin a) R}
    (h : (1 : Matrix (Fin a) (Fin a) R) + c • x = 1 + c • y) : x = y := by
  have h' : c • x = c • y := add_left_cancel h
  ext i j
  have := congrArg (fun M => M i j) h'
  simp only [Matrix.smul_apply, smul_eq_mul] at this
  exact mul_left_cancel₀ hc this

variable {A : Type} [AddCommGroup A]

theorem one_add_smul_mul (x y : Matrix (Fin a) (Fin a) R) :
    ((1 : Matrix (Fin a) (Fin a) R) + c • x) * (1 + c • y) = 1 + c • (x + y + c • (x * y)) := by
  simp only [add_mul, mul_add, one_mul, mul_one, smul_add, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul]
  abel

noncomputable def congChar (hc : c ≠ 0) (φ : R →+ A) (hφ : ∀ x, φ (c * x) = 0)
    (B : Matrix (Fin a) (Fin a) R) :
    (Matrix.GeneralLinearGroup.map (n := Fin a) (Ideal.Quotient.mk (Ideal.span {c}))).ker →*
      Multiplicative A :=
  MonoidHom.mk' (fun g => Multiplicative.ofAdd (φ (B * Classical.choose (exists_eq_one_add_smul g)).trace))
    (by
      intro g h
      have hg := Classical.choose_spec (exists_eq_one_add_smul g)
      have hh := Classical.choose_spec (exists_eq_one_add_smul h)
      have hgh := Classical.choose_spec (exists_eq_one_add_smul (g * h))
      set x := Classical.choose (exists_eq_one_add_smul g)
      set y := Classical.choose (exists_eq_one_add_smul h)
      set z := Classical.choose (exists_eq_one_add_smul (g * h))
      have hz : z = x + y + c • (x * y) := by
        apply smul_injective hc
        rw [← hgh, ← one_add_smul_mul, ← hg, ← hh]
        rfl
      show Multiplicative.ofAdd _ = Multiplicative.ofAdd _ * Multiplicative.ofAdd _
      rw [← ofAdd_add, hz]
      congr 1
      rw [mul_add, mul_add, Matrix.trace_add, Matrix.trace_add, map_add, map_add,
        Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, hφ, add_zero])

theorem congChar_apply (hc : c ≠ 0) (φ : R →+ A) (hφ : ∀ x, φ (c * x) = 0)
    (B : Matrix (Fin a) (Fin a) R) (g) (x : Matrix (Fin a) (Fin a) R)
    (hx : (g.1 : Matrix (Fin a) (Fin a) R) = 1 + c • x) :
    congChar hc φ hφ B g = Multiplicative.ofAdd (φ (B * x).trace) := by
  have hs := Classical.choose_spec (exists_eq_one_add_smul g)
  have : Classical.choose (exists_eq_one_add_smul g) = x := smul_injective hc (hs.symm.trans hx)
  simp only [congChar, MonoidHom.mk'_apply, this]

end GlobalTheory.CongChar

namespace GlobalTheory

theorem congChar_exists : ∀ (R A : Type) [CommRing R] [IsDomain R] [AddCommGroup A] (a : ℕ) (c : R), c ≠ 0 → ∀ (φ : R →+ A), (∀ x, φ (c * x) = 0) → ∀ B : Matrix (Fin a) (Fin a) R, ∃ lam : (Matrix.GeneralLinearGroup.map (n := Fin a) (Ideal.Quotient.mk (Ideal.span {c}))).ker →* Multiplicative A, ∀ g (x : Matrix (Fin a) (Fin a) R), (g.1 : Matrix (Fin a) (Fin a) R) = 1 + c • x → lam g = Multiplicative.ofAdd (φ (B * x).trace) := by
  intro R A _ _ _ a c hc φ hφ B
  exact ⟨CongChar.congChar hc φ hφ B, fun g x hx => CongChar.congChar_apply hc φ hφ B g x hx⟩

end GlobalTheory
