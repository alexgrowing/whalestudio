import Mathlib
open MvPolynomial

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.DPEval2

def bv (p : ℕ × ℕ) : MvPolynomial (Fin 2) ℚ :=
  ((p.1.factorial : ℚ)⁻¹ • (X 0 : MvPolynomial (Fin 2) ℚ) ^ p.1) * ((p.2.factorial : ℚ)⁻¹ • X 1 ^ p.2)

def ex (p : ℕ × ℕ) : Fin 2 →₀ ℕ := Finsupp.single 0 p.1 + Finsupp.single 1 p.2

theorem ex_injective : Function.Injective ex := by
  intro p q h
  have h0 := congrArg (fun f : Fin 2 →₀ ℕ ↦ f 0) h
  have h1 := congrArg (fun f : Fin 2 →₀ ℕ ↦ f 1) h
  simp [ex] at h0 h1
  exact Prod.ext h0 h1

theorem bv_eq (p : ℕ × ℕ) :
    bv p = ((p.1.factorial : ℚ)⁻¹ * (p.2.factorial : ℚ)⁻¹) • monomial (ex p) (1 : ℚ) := by
  rw [bv, ex, X_pow_eq_monomial, X_pow_eq_monomial, smul_monomial, smul_monomial, monomial_mul,
    smul_monomial]
  simp

theorem bv_li : LinearIndependent ℚ bv := by
  have h := ((basisMonomials (Fin 2) ℚ).linearIndependent.comp ex ex_injective).units_smul
    (fun p : ℕ × ℕ ↦ Units.mk0 ((p.1.factorial : ℚ)⁻¹ * (p.2.factorial : ℚ)⁻¹) (by positivity))
  have e : bv = (fun p : ℕ × ℕ ↦ Units.mk0 ((p.1.factorial : ℚ)⁻¹ * (p.2.factorial : ℚ)⁻¹) (by positivity)) •
      (⇑(basisMonomials (Fin 2) ℚ) ∘ ex) := by
    funext p
    simp [bv_eq, Units.smul_def, coe_basisMonomials]
  rw [e]; exact h

theorem ex_add (p q : ℕ × ℕ) : ex (p + q) = ex p + ex q := by
  simp only [ex, Prod.fst_add, Prod.snd_add, Finsupp.single_add]; abel

theorem bv_mul (p q : ℕ × ℕ) :
    bv p * bv q = ((p.1 + q.1).choose p.1 * (p.2 + q.2).choose p.2 : ℕ) • bv (p + q) := by
  rw [bv_eq, bv_eq, bv_eq, smul_mul_smul, monomial_mul, ← ex_add, ← Nat.cast_smul_eq_nsmul ℚ, smul_smul,
    mul_one]
  congr 1
  simp only [Prod.fst_add, Prod.snd_add, Nat.cast_mul, Nat.cast_add_choose]
  field_simp

def D : Submodule ℤ (MvPolynomial (Fin 2) ℚ) := Submodule.span ℤ (Set.range bv)

theorem bv_mem (p : ℕ × ℕ) : bv p ∈ D := Submodule.subset_span ⟨p, rfl⟩

def β : Module.Basis (ℕ × ℕ) ℤ D := Module.Basis.span (bv_li.restrict_scalars' ℤ)

theorem β_eq (p : ℕ × ℕ) : β p = ⟨bv p, bv_mem p⟩ :=
  Module.Basis.span_apply _ p

theorem mul_mem {x y : MvPolynomial (Fin 2) ℚ} (hx : x ∈ D) (hy : y ∈ D) : x * y ∈ D := by
  refine Submodule.span_induction₂ (p := fun x y _ _ ↦ x * y ∈ D) ?_ ?_ ?_ ?_ ?_ ?_ ?_ hx hy
  · rintro _ _ ⟨m, rfl⟩ ⟨n, rfl⟩
    rw [bv_mul]
    exact Submodule.smul_of_tower_mem _ _ (bv_mem _)
  · intro y _; simp
  · intro y _; simp
  · intro x y z _ _ _ h1 h2; rw [add_mul]; exact add_mem h1 h2
  · intro x y z _ _ _ h1 h2; rw [mul_add]; exact add_mem h1 h2
  · intro r x y _ _ h; rw [smul_mul_assoc]; exact Submodule.smul_mem _ _ h
  · intro r x y _ _ h; rw [mul_smul_comm]; exact Submodule.smul_mem _ _ h

variable {B : Type} [CommRing B] (u v : ℕ → B)

def ψ : D →ₗ[ℤ] B := β.constr ℤ fun p ↦ u p.1 * v p.2

open Classical in

def φ (q : MvPolynomial (Fin 2) ℚ) : B := if h : q ∈ D then ψ u v ⟨q, h⟩ else 0

theorem φ_of_mem {q : MvPolynomial (Fin 2) ℚ} (h : q ∈ D) : φ u v q = ψ u v ⟨q, h⟩ := dif_pos h

theorem φ_bv (p : ℕ × ℕ) : φ u v (bv p) = u p.1 * v p.2 := by
  rw [φ_of_mem u v (bv_mem p), ← β_eq, ψ, Module.Basis.constr_basis]

theorem φ_add {x y : MvPolynomial (Fin 2) ℚ} (hx : x ∈ D) (hy : y ∈ D) :
    φ u v (x + y) = φ u v x + φ u v y := by
  rw [φ_of_mem u v hx, φ_of_mem u v hy, φ_of_mem u v (add_mem hx hy), ← map_add]; rfl

theorem φ_zsmul (z : ℤ) {x : MvPolynomial (Fin 2) ℚ} (hx : x ∈ D) : φ u v (z • x) = z • φ u v x := by
  rw [φ_of_mem u v hx, φ_of_mem u v (Submodule.smul_mem _ z hx), ← map_zsmul]; rfl

theorem φ_nsmul (n : ℕ) {x : MvPolynomial (Fin 2) ℚ} (hx : x ∈ D) : φ u v (n • x) = n • φ u v x := by
  rw [← Nat.cast_smul_eq_nsmul ℤ n x, φ_zsmul u v _ hx, Nat.cast_smul_eq_nsmul]

theorem φ_zero : φ u v 0 = 0 := by
  rw [φ_of_mem u v (zero_mem _)]; exact map_zero (ψ u v)

theorem φ_mul (hu : ∀ m n, u m * u n = ((m + n).choose m : B) * u (m + n))
    (hv : ∀ m n, v m * v n = ((m + n).choose m : B) * v (m + n))
    {x y : MvPolynomial (Fin 2) ℚ} (hx : x ∈ D) (hy : y ∈ D) :
    φ u v (x * y) = φ u v x * φ u v y := by
  refine Submodule.span_induction₂ (p := fun x y hx hy ↦ φ u v (x * y) = φ u v x * φ u v y)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ hx hy
  · rintro _ _ ⟨p, rfl⟩ ⟨q, rfl⟩
    rw [bv_mul, φ_nsmul u v _ (bv_mem _), φ_bv, φ_bv, φ_bv, nsmul_eq_mul]
    calc ((((p.1 + q.1).choose p.1 * (p.2 + q.2).choose p.2 : ℕ)) : B) * (u (p + q).1 * v (p + q).2)
        = (((p.1 + q.1).choose p.1 : B) * u (p.1 + q.1)) * (((p.2 + q.2).choose p.2 : B) * v (p.2 + q.2)) := by
          simp only [Prod.fst_add, Prod.snd_add, Nat.cast_mul]; ring
      _ = u p.1 * v p.2 * (u q.1 * v q.2) := by rw [← hu, ← hv]; ring
  · intro y _; simp [φ_zero]
  · intro y _; simp [φ_zero]
  · intro x y z hx hy hz h1 h2
    rw [add_mul, φ_add u v (mul_mem hx hz) (mul_mem hy hz), φ_add u v hx hy, h1, h2, add_mul]
  · intro x y z hx hy hz h1 h2
    rw [mul_add, φ_add u v (mul_mem hx hy) (mul_mem hx hz), φ_add u v hy hz, h1, h2, mul_add]
  · intro r x y hx hy h
    rw [smul_mul_assoc, φ_zsmul u v r (mul_mem hx hy), φ_zsmul u v r hx, h, smul_mul_assoc]
  · intro r x y hx hy h
    rw [mul_smul_comm, φ_zsmul u v r (mul_mem hx hy), φ_zsmul u v r hy, h, mul_smul_comm]

end GlobalTheory.DPEval2

namespace GlobalTheory

open DPEval2 in

theorem dpEval_two :
    ∀ (B : Type) [CommRing B] (u v : ℕ → B), u 0 = 1 → v 0 = 1 →
    (∀ m n, u m * u n = ((m + n).choose m : B) * u (m + n)) →
    (∀ m n, v m * v n = ((m + n).choose m : B) * v (m + n)) →
    ∃ φ : MvPolynomial (Fin 2) ℚ → B,
      (∀ a c : ℕ, φ (((a.factorial : ℚ)⁻¹ • MvPolynomial.X 0 ^ a) * ((c.factorial : ℚ)⁻¹ • MvPolynomial.X 1 ^ c)) = u a * v c) ∧
      (∀ d ∈ Submodule.span ℤ (Set.range fun p : ℕ × ℕ ↦ ((p.1.factorial : ℚ)⁻¹ • (MvPolynomial.X 0 : MvPolynomial (Fin 2) ℚ) ^ p.1) * ((p.2.factorial : ℚ)⁻¹ • MvPolynomial.X 1 ^ p.2)),
        ∀ e ∈ Submodule.span ℤ (Set.range fun p : ℕ × ℕ ↦ ((p.1.factorial : ℚ)⁻¹ • (MvPolynomial.X 0 : MvPolynomial (Fin 2) ℚ) ^ p.1) * ((p.2.factorial : ℚ)⁻¹ • MvPolynomial.X 1 ^ p.2)),
          φ (d + e) = φ d + φ e ∧
          d * e ∈ Submodule.span ℤ (Set.range fun p : ℕ × ℕ ↦ ((p.1.factorial : ℚ)⁻¹ • (MvPolynomial.X 0 : MvPolynomial (Fin 2) ℚ) ^ p.1) * ((p.2.factorial : ℚ)⁻¹ • MvPolynomial.X 1 ^ p.2)) ∧
          φ (d * e) = φ d * φ e) ∧
      (∀ z : ℤ, ∀ d ∈ Submodule.span ℤ (Set.range fun p : ℕ × ℕ ↦ ((p.1.factorial : ℚ)⁻¹ • (MvPolynomial.X 0 : MvPolynomial (Fin 2) ℚ) ^ p.1) * ((p.2.factorial : ℚ)⁻¹ • MvPolynomial.X 1 ^ p.2)),
        φ (z • d) = z • φ d) := by
  intro B _ u v _ _ hu hv
  refine ⟨φ u v, fun a c ↦ φ_bv u v (a, c), fun d hd e he ↦ ?_, fun z d hd ↦ φ_zsmul u v z hd⟩
  exact ⟨φ_add u v hd he, mul_mem hd he, φ_mul u v hu hv hd he⟩

end GlobalTheory
