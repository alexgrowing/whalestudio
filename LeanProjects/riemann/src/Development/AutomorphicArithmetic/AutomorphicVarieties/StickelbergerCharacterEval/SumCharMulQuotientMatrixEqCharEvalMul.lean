import Development.AutomorphicArithmetic.AutomorphicVarieties.StickelbergerCharacterEval.MemZpowersIff

open Finset UpperTheory.V.Bern UpperTheory.V.B4 UpperTheory.V.B5

private theorem ev_eq_sum {A : Type} [CommRing A] {Ω : Type} [Field Ω] [Algebra A Ω] {Γ : Type} [CommGroup Γ] [Fintype Γ]
    (χ : Γ →* Ωˣ) (z : MonoidAlgebra A Γ) :
    ev A χ z = ∑ g, algebraMap A Ω (z.coeff g) * ((χ g : Ωˣ) : Ω) := by
  classical
  induction z using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => simp [hx, hy, add_mul, Finset.sum_add_distrib]
  | single g n =>
    rw [ev_single, Finset.sum_eq_single g]
    · simp
    · intro b _ hb
      simp [Finsupp.single_apply, hb, hb.symm]
    · simp

theorem UpperTheory.V.B5.sum_char_mul_quotientMatrix_eq_charEval_mul :
    ∀ {A : Type} [CommRing A] {Ω : Type} [Field Ω] [Algebra A Ω] {Γ : Type} [CommGroup Γ] [Finite Γ] (c : Γ) (ε : ℤ), c * c = 1 → c ≠ 1 → ∀ (χ : Ch Ω c ε) (z : MonoidAlgebra A Γ) (j : Qc c), ∑ i : Qc c, ((χ.1 (rep i) : Ωˣ) : Ω) * algebraMap A Ω (mat c ε z i j) = ev A χ.1 z * ((χ.1 (rep j) : Ωˣ) : Ω) := by
  intro A _ Ω _ _ Γ _ _ c ε h2 h1 χ z j
  have := Fintype.ofFinite Γ
  have hc : ((χ.1 c : Ωˣ) : Ω) = (ε : Ω) := χ.2
  rw [ev_eq_sum, Finset.sum_mul, ← Equiv.sum_comp (Equiv.mulRight (rep j)⁻¹), sum_rep h2 h1]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hj : ((χ.1 (rep j) : Ωˣ) : Ω) ≠ 0 := Units.ne_zero _
  simp only [mat, Matrix.of_apply, Equiv.coe_mulRight, map_add, map_mul, map_intCast, mul_assoc, map_inv,
    Units.val_mul, Units.val_inv_eq_inv_val, hc, inv_mul_cancel₀ hj]
  ring
