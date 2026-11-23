import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.GramParity

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem ordL_spec {x : L} (hx : x ≠ 0) :
    Valued.v x = ((Multiplicative.ofAdd (-ordL x) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
  have h : Valued.v x ≠ 0 := (Valuation.ne_zero_iff _).mpr hx
  unfold ordL
  rw [dif_neg h]
  simp

theorem ordL_eq_of {x : L} (hx : x ≠ 0) {a : ℤ}
    (h : Valued.v x = ((Multiplicative.ofAdd (-a) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))) :
    ordL x = a := by
  have h2 := (ordL_spec hx).symm.trans h
  have h3 := WithZero.coe_injective h2
  simpa using h3

theorem ordL_mul {x y : L} (hx : x ≠ 0) (hy : y ≠ 0) : ordL (x * y) = ordL x + ordL y := by
  apply ordL_eq_of (mul_ne_zero hx hy)
  rw [Valuation.map_mul, ordL_spec hx, ordL_spec hy, ← WithZero.coe_mul, ← ofAdd_add]
  congr 2
  ring

theorem ordL_eq_zero_of_v_one {x : L} (h : Valued.v x = 1) : ordL x = 0 := by
  have hx : x ≠ 0 := by
    intro h0; rw [h0, Valuation.map_zero] at h; exact zero_ne_one h
  apply ordL_eq_of hx
  rw [h]; rfl

theorem ordL_congr {x y : L} (h : Valued.v x = Valued.v y) : ordL x = ordL y := by
  unfold ordL
  simp only [h]

end GlobalTheory.GramParity

namespace GlobalTheory.GramParity

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem gram_eq {n : ℕ} {α : Type} [Fintype α] (σ : L →+* L) (f : α → Fin n → L) :
    (Matrix.of fun i j => ∑ k, σ (f i k) * f j k) =
      (Matrix.of fun i k => f i k).map σ * (Matrix.of fun i k => f i k)ᵀ := by
  ext i j
  simp [Matrix.mul_apply]

theorem coords_eq {n : ℕ} (V : Submodule L (Fin n → L)) {ι : Type} [Fintype ι] [DecidableEq ι]
    (b c : Module.Basis ι L V) :
    (Matrix.of fun i k => (b i : Fin n → L) k) =
      (c.toMatrix b)ᵀ * (Matrix.of fun i k => (c i : Fin n → L) k) := by
  ext i k
  have h := c.sum_repr (b i)
  have h2 := congrArg (fun v : V => (v : Fin n → L) k) h
  simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h2
  simp [Matrix.mul_apply, Module.Basis.toMatrix_apply, ← h2]

theorem det_gram_change {n : ℕ} (σ : L →+* L) (V : Submodule L (Fin n → L)) {ι : Type} [Fintype ι]
    [DecidableEq ι] (b c : Module.Basis ι L V) :
    (Matrix.of fun i j => ∑ k, σ ((b i : Fin n → L) k) * (b j : Fin n → L) k).det =
      σ (c.toMatrix b).det *
        (Matrix.of fun i j => ∑ k, σ ((c i : Fin n → L) k) * (c j : Fin n → L) k).det *
        (c.toMatrix b).det := by
  rw [gram_eq σ (fun i => (b i : Fin n → L)), gram_eq σ (fun i => (c i : Fin n → L))]
  rw [coords_eq V b c]
  rw [Matrix.map_mul, Matrix.transpose_mul, Matrix.transpose_transpose]
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc ((of fun i k ↦ ((c i : V) : Fin n → L) k).map σ), ← Matrix.mul_assoc,
    Matrix.det_mul, Matrix.det_mul]
  congr 2
  rw [RingHom.map_det, ← Matrix.det_transpose]
  rfl

end GlobalTheory.GramParity

namespace GlobalTheory.GramParity

theorem gram_parity_gen {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]
    (σ : L →+* L) (hσ : ∀ x, Valued.v (σ x) = Valued.v x) (n : ℕ) (V : Submodule L (Fin n → L))
    {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (b : Module.Basis ι L V)
    (c : Module.Basis κ L V)
    (hc : Valued.v (Matrix.of fun i j => ∑ k, σ ((c i : Fin n → L) k) * (c j : Fin n → L) k).det = 1) :
    (-1 : ℂ) ^ ordL (Matrix.of fun i j => ∑ k, σ ((b i : Fin n → L) k) * (b j : Fin n → L) k).det = 1 := by
  set e : ι ≃ κ := b.indexEquiv c
  set c' : Module.Basis ι L V := c.reindex e.symm
  have hc' : (Matrix.of fun i j => ∑ k, σ ((c' i : Fin n → L) k) * (c' j : Fin n → L) k).det =
      (Matrix.of fun i j => ∑ k, σ ((c i : Fin n → L) k) * (c j : Fin n → L) k).det := by
    rw [← Matrix.det_submatrix_equiv_self e]
    congr 1
    ext i j
    simp [c', Module.Basis.reindex_apply]
  have hg1 : Valued.v (Matrix.of fun i j => ∑ k, σ ((c' i : Fin n → L) k) * (c' j : Fin n → L) k).det = 1 := by
    rw [hc', hc]
  have hg0 : (Matrix.of fun i j => ∑ k, σ ((c' i : Fin n → L) k) * (c' j : Fin n → L) k).det ≠ 0 := by
    intro h0; rw [h0, Valuation.map_zero] at hg1; exact zero_ne_one hg1
  have hd : (c'.toMatrix b).det ≠ 0 := by
    have := c'.invertibleToMatrix b
    exact (Matrix.isUnit_det_of_invertible _).ne_zero
  have hσd : σ (c'.toMatrix b).det ≠ 0 := (map_ne_zero σ).mpr hd
  rw [det_gram_change σ V b c', ordL_mul (mul_ne_zero hσd hg0) hd, ordL_mul hσd hg0,
    ordL_eq_zero_of_v_one hg1, ordL_congr (hσ _)]
  have : ordL (c'.toMatrix b).det + 0 + ordL (c'.toMatrix b).det = 2 * ordL (c'.toMatrix b).det := by ring
  rw [this, _root_.zpow_mul]
  norm_num

end GlobalTheory.GramParity

open GlobalTheory.GramParity in
theorem GlobalTheory.GramParity.gram_det_parity : ∀ (E : Type) [Field E] [NumberField E] (w : Pl E) (σ : w.adicCompletion E →+* w.adicCompletion E),
    (∀ x, Valued.v (σ x) = Valued.v x) → ∀ (n : ℕ) (V : Submodule (w.adicCompletion E) (Fin n → w.adicCompletion E))
    {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (b : Module.Basis ι (w.adicCompletion E) V)
    (c : Module.Basis κ (w.adicCompletion E) V),
    Valued.v (Matrix.of fun i j => ∑ k, σ ((c i : Fin n → w.adicCompletion E) k) * (c j : Fin n → w.adicCompletion E) k).det = 1 →
    (-1 : ℂ) ^ ordL (Matrix.of fun i j => ∑ k, σ ((b i : Fin n → w.adicCompletion E) k) * (b j : Fin n → w.adicCompletion E) k).det = 1 := by
  intro E _ _ w σ hσ n V ι κ _ _ _ _ b c hc
  exact gram_parity_gen σ hσ n V b c hc
