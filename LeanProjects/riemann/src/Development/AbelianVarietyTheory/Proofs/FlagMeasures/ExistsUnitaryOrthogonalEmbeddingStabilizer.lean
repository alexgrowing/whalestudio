import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsFinEmb

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.GaussMean GlobalTheory.StabUnfold
open scoped TensorProduct

namespace GlobalTheory.StabRing

open Formalism.UG

theorem cT_add_rect {R : Type} [CommRing R] (σ : R →+* R) {a b : Type} (M N : Matrix a b R) :
    cT σ (M + N) = cT σ M + cT σ N := by
  ext i j; simp [cT]

theorem exists_emb_block {R : Type} [CommRing R] (σ : R →+* R) {n m k : Type}
    [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m] [Fintype k] [DecidableEq k]
    (J : Matrix n n R) (J' : Matrix m m R) (X : Matrix n k R) (U : Matrix k n R)
    (A : Matrix n m R) (A' : Matrix m n R)
    (hB : IsUnit (cT σ X * J * X)) (hXA : cT σ X * J * A = 0) (hAX : cT σ A * J * X = 0)
    (hJ : cT σ A * J * A = J') (h1 : A' * A = 1) (h2 : A' * X = 0) (h3 : U * A = 0) (h4 : U * X = 1)
    (h5 : X * U + A * A' = 1) :
    ∃ j : UJ σ J' →* UJ σ J,
      (∀ g, ((j g : GL n R) : Matrix n n R) = X * U + A * ((g : GL m R) : Matrix m m R) * A') ∧
      ∀ h : UJ σ J, ((h : GL n R) : Matrix n n R) * X = X → h ∈ j.range := by
  have hmul : ∀ g g' : Matrix m m R,
      (X * U + A * g * A') * (X * U + A * g' * A') = X * U + A * (g * g') * A' := by
    intro g g'
    calc (X * U + A * g * A') * (X * U + A * g' * A')
        = X * (U * X) * U + X * (U * A) * g' * A' + (A * g * (A' * X) * U + A * g * (A' * A) * g' * A') := by
          simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc]; abel
      _ = _ := by rw [h1, h2, h3, h4]; simp [Matrix.mul_assoc]
  have hone : X * U + A * (1 : Matrix m m R) * A' = 1 := by rw [Matrix.mul_one, h5]
  have hform : ∀ g : Matrix m m R, cT σ (X * U + A * g * A') * J * (X * U + A * g * A')
      = cT σ U * (cT σ X * J * X) * U + cT σ A' * (cT σ g * J' * g) * A' := by
    intro g
    calc cT σ (X * U + A * g * A') * J * (X * U + A * g * A')
        = cT σ U * (cT σ X * J * X) * U + cT σ U * (cT σ X * J * A) * g * A'
          + (cT σ A' * cT σ g * (cT σ A * J * X) * U
            + cT σ A' * (cT σ g * (cT σ A * J * A) * g) * A') := by
          simp only [cT_add_rect, cT_mul, Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc]; abel
      _ = _ := by rw [hXA, hAX, hJ]; simp
  have hJJ : cT σ U * (cT σ X * J * X) * U + cT σ A' * J' * A' = J := by
    have := hform 1
    rw [hone] at this
    simpa [cT_one] using this.symm
  let j0 : GL m R → GL n R := fun g =>
    ⟨X * U + A * (g : Matrix m m R) * A', X * U + A * ((g⁻¹ : GL m R) : Matrix m m R) * A',
      by rw [hmul, Units.mul_inv, hone], by rw [hmul, Units.inv_mul, hone]⟩
  have hmem : ∀ g : UJ σ J', j0 g ∈ UJ σ J := by
    intro g
    have hg : cT σ ((g : GL m R) : Matrix m m R) * J' * ((g : GL m R) : Matrix m m R) = J' := g.2
    change cT σ (X * U + A * ((g : GL m R) : Matrix m m R) * A') * J
      * (X * U + A * ((g : GL m R) : Matrix m m R) * A') = J
    rw [hform, hg, hJJ]
  let j : UJ σ J' →* UJ σ J :=
    { toFun := fun g => ⟨j0 g, hmem g⟩
      map_one' := by
        apply Subtype.ext; apply Units.ext
        exact hone
      map_mul' := by
        intro g g'
        apply Subtype.ext; apply Units.ext
        exact (hmul _ _).symm }
  refine ⟨j, fun g => rfl, ?_⟩
  have hXJ : cT σ X * J = cT σ X * J * X * U := by
    calc cT σ X * J = cT σ X * J * (X * U + A * A') := by rw [h5, Matrix.mul_one]
      _ = cT σ X * J * X * U + cT σ X * J * A * A' := by
        simp only [Matrix.mul_add, Matrix.mul_assoc]
      _ = _ := by rw [hXA]; simp
  have key : ∀ h : Matrix n n R, cT σ h * J * h = J → h * X = X → A * (A' * h * A) = h * A := by
    intro h hh hX
    have e1 : cT σ X * J * X * (U * h * A) = 0 := by
      calc cT σ X * J * X * (U * h * A) = (cT σ X * J * X * U) * h * A := by
            simp only [Matrix.mul_assoc]
        _ = cT σ (h * X) * J * h * A := by rw [← hXJ, hX]
        _ = cT σ X * (cT σ h * J * h) * A := by simp only [cT_mul, Matrix.mul_assoc]
        _ = 0 := by rw [hh, hXA]
    have e2 : U * h * A = 0 := by
      obtain ⟨b, hb⟩ := hB
      rw [← hb] at e1
      calc U * h * A = ((b⁻¹ : GL k R) : Matrix k k R) * (b : Matrix k k R) * (U * h * A) := by
            rw [Units.inv_mul, Matrix.one_mul]
        _ = 0 := by rw [Matrix.mul_assoc, e1, Matrix.mul_zero]
    calc A * (A' * h * A) = X * (U * h * A) + A * (A' * h * A) := by rw [e2]; simp
      _ = (X * U + A * A') * h * A := by simp only [Matrix.add_mul, Matrix.mul_assoc]
      _ = h * A := by rw [h5, Matrix.one_mul]
  intro h hX
  have hh : cT σ ((h : GL n R) : Matrix n n R) * J * ((h : GL n R) : Matrix n n R) = J := h.2
  have hh' : cT σ (((h : GL n R)⁻¹ : GL n R) : Matrix n n R) * J
      * (((h : GL n R)⁻¹ : GL n R) : Matrix n n R) = J := (h⁻¹).2
  have hX' : (((h : GL n R)⁻¹ : GL n R) : Matrix n n R) * X = X := by
    conv_lhs => rw [← hX]
    rw [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
  have k1 := key _ hh hX
  have k2 := key _ hh' hX'
  let g : GL m R := ⟨A' * ((h : GL n R) : Matrix n n R) * A,
    A' * (((h : GL n R)⁻¹ : GL n R) : Matrix n n R) * A,
    by rw [Matrix.mul_assoc _ A, k2, Matrix.mul_assoc A', ← Matrix.mul_assoc _ _ A, Units.mul_inv,
      Matrix.one_mul, h1],
    by rw [Matrix.mul_assoc _ A, k1, Matrix.mul_assoc A', ← Matrix.mul_assoc _ _ A, Units.inv_mul,
      Matrix.one_mul, h1]⟩
  have hg : g ∈ UJ σ J' := by
    change cT σ (A' * ((h : GL n R) : Matrix n n R) * A) * J'
      * (A' * ((h : GL n R) : Matrix n n R) * A) = J'
    calc cT σ (A' * ((h : GL n R) : Matrix n n R) * A) * J' * (A' * ((h : GL n R) : Matrix n n R) * A)
        = cT σ (A * (A' * ((h : GL n R) : Matrix n n R) * A)) * J
          * (A * (A' * ((h : GL n R) : Matrix n n R) * A)) := by
          rw [cT_mul σ A, ← hJ]; simp only [Matrix.mul_assoc]
      _ = cT σ A * (cT σ ((h : GL n R) : Matrix n n R) * J * ((h : GL n R) : Matrix n n R)) * A := by
          rw [k1]; simp only [cT_mul, Matrix.mul_assoc]
      _ = J' := by rw [hh, hJ]
  refine ⟨⟨g, hg⟩, ?_⟩
  apply Subtype.ext; apply Units.ext
  change X * U + A * (A' * ((h : GL n R) : Matrix n n R) * A) * A' = ((h : GL n R) : Matrix n n R)
  rw [k1]
  calc X * U + ((h : GL n R) : Matrix n n R) * A * A'
      = ((h : GL n R) : Matrix n n R) * X * U + ((h : GL n R) : Matrix n n R) * A * A' := by rw [hX]
    _ = ((h : GL n R) : Matrix n n R) * (X * U + A * A') := by
      simp only [Matrix.mul_add, Matrix.mul_assoc]
    _ = _ := by rw [h5, Matrix.mul_one]

theorem exists_emb : ∀ (R : Type) [CommRing R] (σ : R →+* R) (n m : ℕ) (J : Matrix (Fin n) (Fin n) R) (J' : Matrix (Fin m) (Fin m) R) (x u : Fin n → R) (A : Matrix (Fin n) (Fin m) R) (A' : Matrix (Fin m) (Fin n) R), IsUnit ((fun i => σ (x i)) ⬝ᵥ (J *ᵥ x)) → (fun i => σ (x i)) ᵥ* (J * A) = 0 → Formalism.UG.cT σ A *ᵥ (J *ᵥ x) = 0 → Formalism.UG.cT σ A * J * A = J' → A' * A = 1 → A' *ᵥ x = 0 → u ᵥ* A = 0 → u ⬝ᵥ x = 1 → vecMulVec x u + A * A' = 1 → ∃ j : Formalism.UG.UJ σ J' →* Formalism.UG.UJ σ J, (∀ g, ((j g : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) = vecMulVec x u + A * ((g : GL (Fin m) R) : Matrix (Fin m) (Fin m) R) * A') ∧ ∀ h : Formalism.UG.UJ σ J, ((h : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) *ᵥ x = x → h ∈ j.range := by
  intro R _ σ n m J J' x u A A' hB hXA hAX hJ h1 h2 h3 h4 h5
  have hc : cT σ (replicateCol Unit x) = replicateRow Unit (fun i => σ (x i)) := by
    ext i j; simp [cT]
  rw [vecMulVec_eq Unit] at h5 ⊢
  obtain ⟨j, hj1, hj2⟩ := exists_emb_block σ J J' (replicateCol Unit x) (replicateRow Unit u) A A'
    (by
      rw [hc, Matrix.mul_assoc, ← replicateCol_mulVec, replicateRow_mul_replicateCol,
        Matrix.isUnit_iff_isUnit_det]
      simpa using hB)
    (by rw [hc, Matrix.mul_assoc, ← replicateRow_vecMul, hXA]; simp)
    (by rw [Matrix.mul_assoc, ← replicateCol_mulVec, ← replicateCol_mulVec, hAX]; simp)
    hJ h1
    (by rw [← replicateCol_mulVec, h2]; simp)
    (by rw [← replicateRow_vecMul, h3]; simp)
    (by rw [replicateRow_mul_replicateCol, h4]; ext i j; simp)
    h5
  exact ⟨j, hj1, fun h hx => hj2 h (by rw [← replicateCol_mulVec, hx])⟩

end GlobalTheory.StabRing
