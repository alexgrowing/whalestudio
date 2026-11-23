import Formalism.LocalToGlobal.Columns.QthExistsBound

open NumberField IsDedekindDomain

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

section Close

variable {E : Type} [Field E] [NumberField E] [StarRing E] (P : HeightOneSpectrum (𝓞 E)) (q : ℕ) (hq0 : (q : E) ≠ 0)

theorem qth_vq_le : P.valuation E (q : E) ≤ 1 := by
  exact (qth_intAt_iff P _).1 ⟨(q : 𝓞 E), 1, fun h => P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h),
    by simp⟩

theorem qth_mulVec {m : ℕ} (W : Sp E m ≃ₗ[E] Sp E m) (x : Sp E m) :
    W x = x + (((toGLm E m W : GL (Fin m) E) : Matrix (Fin m) (Fin m) E) - 1).mulVec x := by
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, toGLm_mulVec]
  abel

include hq0 in
theorem qth_close_scl {m : ℕ} (e : ℕ → ℤ) (he : ∀ l, e l = 0 ∨ e l = 1) (W : Sp E m ≃ₗ[E] Sp E m)
    (hW : ∀ i j, P.valuation E ((((toGLm E m W : GL (Fin m) E) : Matrix (Fin m) (Fin m) E) - 1) i j) ≤ P.valuation E (q : E))
    {x : Sp E m} (hx : x ∈ LocE.sclLat P q m e) : W x ∈ LocE.sclLat P q m e := by
  rw [ciMem_sclLat] at hx ⊢
  intro l
  rw [qth_intAt_iff, qth_mulVec W x]
  set M := ((toGLm E m W : GL (Fin m) E) : Matrix (Fin m) (Fin m) E) with hM
  have hyj : ∀ j : Fin m, P.valuation E (((q : E) ^ e j.1)⁻¹ * x j) ≤ 1 :=
    fun j => (qth_intAt_iff P _).1 (hx j)
  have hqe : ∀ j : Fin m, P.valuation E ((q : E) ^ (e j.1)) ≤ 1 := by
    intro j
    rcases he j with h | h <;> rw [h]
    · simp
    · rw [zpow_one]
      exact qth_vq_le P q
  have hv0 : P.valuation E (q : E) ≠ 0 := by simpa using hq0
  have hcM : ∀ j, P.valuation E (((q : E) ^ e l.1)⁻¹ * (M - 1) l j) ≤ 1 := by
    intro j
    rcases he l with h | h <;> rw [h]
    · simp only [zpow_zero, inv_one, one_mul]
      exact (hW l j).trans (qth_vq_le P q)
    · rw [zpow_one, map_mul, map_inv₀]
      calc (P.valuation E (q : E))⁻¹ * P.valuation E ((M - 1) l j)
          ≤ (P.valuation E (q : E))⁻¹ * P.valuation E (q : E) := by gcongr; exact hW l j
        _ = 1 := inv_mul_cancel₀ hv0
  have hsplit : ((q : E) ^ e l.1)⁻¹ * (x + (M - 1).mulVec x) l = ((q : E) ^ e l.1)⁻¹ * x l +
      ∑ j, (((q : E) ^ e l.1)⁻¹ * (M - 1) l j) * (q : E) ^ (e j.1) * (((q : E) ^ e j.1)⁻¹ * x j) := by
    simp only [Pi.add_apply, Matrix.mulVec, dotProduct, mul_add, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    have hz : (q : E) ^ (e j.1) ≠ 0 := zpow_ne_zero _ hq0
    have h1 : (q : E) ^ (e j.1) * (((q : E) ^ (e j.1))⁻¹ * x j) = x j := by
      rw [← mul_assoc, mul_inv_cancel₀ hz, one_mul]
    rw [mul_assoc _ ((q : E) ^ (e j.1)), h1]
    ring
  rw [hsplit]
  refine Valuation.map_add_le _ (hyj l) (Valuation.map_sum_le _ fun j _ => ?_)
  rw [map_mul, map_mul]
  exact mul_le_one' (mul_le_one' (hcM j) (hqe j)) (hyj j)

include hq0 in
theorem qth_close_std {m : ℕ} (W : Sp E m ≃ₗ[E] Sp E m)
    (hW : ∀ i j, P.valuation E ((((toGLm E m W : GL (Fin m) E) : Matrix (Fin m) (Fin m) E) - 1) i j) ≤ P.valuation E (q : E))
    {x : Sp E m} (hx : x ∈ stdAt E m P) : W x ∈ stdAt E m P := by
  rw [ciMem_stdAt] at hx ⊢
  intro i
  rw [qth_mulVec W x]
  have hxi : ∀ j, P.valuation E (x j) ≤ 1 := fun j => (qth_intAt_iff P _).1 (hx j)
  rw [qth_intAt_iff]
  show P.valuation E (x i + ∑ j, (((toGLm E m W : GL (Fin m) E) : Matrix (Fin m) (Fin m) E) - 1) i j * x j) ≤ 1
  refine Valuation.map_add_le _ (hxi i) (Valuation.map_sum_le _ fun j _ => ?_)
  rw [map_mul]
  exact mul_le_one' ((hW i j).trans (qth_vq_le P q)) (hxi j)

end Close

end Formalism.L2.Col
