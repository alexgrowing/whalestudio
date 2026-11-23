import Formalism.SatakeDualWeyl.StatementE

open NumberField IsDedekindDomain Formalism.UG

namespace Formalism.UG.P

section Upper

variable {L : Type} [Field L] {n : ℕ}

theorem spherical_upper_iff (b : GL (Fin n) L) :
    (∀ i j : Fin n, j < i → (b : Matrix (Fin n) (Fin n) L) i j = 0) ↔
      (b : Matrix (Fin n) (Fin n) L).BlockTriangular id :=
  ⟨fun h _ _ hij => h _ _ hij, fun h _ _ hij => h hij⟩

theorem spherical_diag_mul (A B : Matrix (Fin n) (Fin n) L) (hA : A.BlockTriangular id)
    (hB : B.BlockTriangular id) (i : Fin n) : (A * B) i i = A i i * B i i := by
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_single i (fun j _ hji => ?_) (by simp)
  rcases lt_or_gt_of_ne hji with h | h
  · rw [hA h, zero_mul]
  · rw [hB h, mul_zero]

theorem spherical_upper_inv (b : GL (Fin n) L) (hb : (b : Matrix (Fin n) (Fin n) L).BlockTriangular id) :
    ((b⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L).BlockTriangular id := by
  have : Invertible (b : Matrix (Fin n) (Fin n) L) := Units.invertible b
  rw [Matrix.coe_units_inv]
  exact Matrix.blockTriangular_inv_of_blockTriangular hb

theorem spherical_upper_mul (b c : GL (Fin n) L) (hb : (b : Matrix (Fin n) (Fin n) L).BlockTriangular id)
    (hc : (c : Matrix (Fin n) (Fin n) L).BlockTriangular id) :
    ((b * c : GL (Fin n) L) : Matrix (Fin n) (Fin n) L).BlockTriangular id := by
  rw [Units.val_mul]; exact hb.mul hc

theorem spherical_diag_ne_zero (b : GL (Fin n) L) (hb : (b : Matrix (Fin n) (Fin n) L).BlockTriangular id)
    (i : Fin n) : (b : Matrix (Fin n) (Fin n) L) i i ≠ 0 := by
  have hd : (b : Matrix (Fin n) (Fin n) L).det ≠ 0 := by
    have := (Matrix.isUnit_iff_isUnit_det _).1 b.isUnit
    exact this.ne_zero
  rw [Matrix.det_of_isUpperTriangular hb] at hd
  exact Finset.prod_ne_zero_iff.1 hd i (Finset.mem_univ _)

end Upper

variable (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

theorem spherical_ordV_mul (x y : v.adicCompletion F)
    (hx : x ≠ 0) (hy : y ≠ 0) : ordV F v (x * y) = ordV F v x + ordV F v y := by
  unfold ordV
  have hx' : Valued.v x ≠ 0 := by simpa using hx
  have hy' : Valued.v y ≠ 0 := by simpa using hy
  have hxy : Valued.v (x * y) ≠ 0 := by simpa using mul_ne_zero hx hy
  rw [dif_neg hx', dif_neg hy', dif_neg hxy]
  have : WithZero.unzero hxy = WithZero.unzero hx' * WithZero.unzero hy' := by
    apply WithZero.coe_injective; simp [WithZero.coe_unzero, map_mul]
  rw [this, toAdd_mul]; ring

theorem spherical_ordV_unit (x y : v.adicCompletion F) (hx : x ∈ Ov F v) (hy : y ∈ Ov F v)
    (hxy : y * x = 1) : ordV F v x = 0 := by
  have hx1 : Valued.v x ≤ 1 := hx
  have hy1 : Valued.v y ≤ 1 := hy
  have hm : Valued.v y * Valued.v x = 1 := by rw [← map_mul, hxy, map_one]
  have h1 : Valued.v x = 1 := by
    refine le_antisymm hx1 ?_
    calc (1 : WithZero (Multiplicative ℤ)) = Valued.v y * Valued.v x := hm.symm
      _ ≤ 1 * Valued.v x := mul_le_mul' hy1 le_rfl
      _ = Valued.v x := one_mul _
  unfold ordV
  have h0 : Valued.v x ≠ 0 := by rw [h1]; exact one_ne_zero
  rw [dif_neg h0]
  have : WithZero.unzero h0 = 1 := by
    apply WithZero.coe_injective; rw [WithZero.coe_unzero, h1]; rfl
  rw [this]; rfl

theorem spherical_qV_ne_zero : (qV F v : ℂ) ≠ 0 := by
  unfold qV
  rw [Nat.cast_ne_zero, Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot

theorem spherical_chiDelta_mul {n : ℕ} (α : Fin n → ℂ) (hα : ∀ i, α i ≠ 0) (b c : GL (Fin n) (v.adicCompletion F))
    (hb : (b : Matrix (Fin n) (Fin n) (v.adicCompletion F)).BlockTriangular id)
    (hc : (c : Matrix (Fin n) (Fin n) (v.adicCompletion F)).BlockTriangular id) :
    chiDelta F v α (b * c) = chiDelta F v α b * chiDelta F v α c := by
  unfold chiDelta
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Units.val_mul, spherical_diag_mul _ _ hb hc i,
    spherical_ordV_mul F v _ _ (spherical_diag_ne_zero b hb i) (spherical_diag_ne_zero c hc i)]
  have hq := spherical_qV_ne_zero F v
  rw [zpow_add₀ (hα i)]
  push_cast
  rw [show (-((ordV F v ((b : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i i) : ℂ) +
      (ordV F v ((c : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i i) : ℂ)) * (((n : ℂ) - 1 - 2 * (i : ℂ)) / 2))
      = (-(ordV F v ((b : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i i) : ℂ) * (((n : ℂ) - 1 - 2 * (i : ℂ)) / 2))
        + (-(ordV F v ((c : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i i) : ℂ) * (((n : ℂ) - 1 - 2 * (i : ℂ)) / 2))
      by ring, Complex.cpow_add _ _ hq]
  ring

theorem spherical_chiDelta_int {n : ℕ} (α : Fin n → ℂ) (b : GL (Fin n) (v.adicCompletion F))
    (hb : (b : Matrix (Fin n) (Fin n) (v.adicCompletion F)).BlockTriangular id)
    (hk : b ∈ GLint (Fin n) (Ov F v)) : chiDelta F v α b = 1 := by
  obtain ⟨k, rfl⟩ := hk
  unfold chiDelta
  refine Finset.prod_eq_one fun i _ => ?_
  have hinv := spherical_upper_inv _ hb
  have hm : ((((bc (n := Fin n) (Ov F v).subtype) k)⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i i *
      (((bc (n := Fin n) (Ov F v).subtype) k : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i i = 1 := by
    rw [← spherical_diag_mul _ _ hinv hb, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_apply_eq]
  have h0 : ordV F v ((((bc (n := Fin n) (Ov F v).subtype) k : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i i) = 0 := by
    refine spherical_ordV_unit F v _ _ ?_ ?_ hm
    · simp only [bc, Units.coe_map]
      exact ((k : Matrix (Fin n) (Fin n) (Ov F v)) i i).2
    · rw [← map_inv (bc (n := Fin n) (Ov F v).subtype) k]
      simp only [bc, Units.coe_map]
      exact (((k⁻¹ : GL (Fin n) (Ov F v)) : Matrix (Fin n) (Fin n) (Ov F v)) i i).2
  rw [h0]; simp

end Formalism.UG.P
