import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CharpolyInt

theorem charpoly_coeff_det_int {E : Type} [Field E] [NumberField E] {n : ℕ} (w : HeightOneSpectrum (𝓞 E))
    (A : Matrix (Fin n) (Fin n) (w.adicCompletion E)) (hA : ∀ i j, A i j ∈ w.adicCompletionIntegers E) :
    (∀ k, A.charpoly.coeff k ∈ w.adicCompletionIntegers E) ∧ A.det ∈ w.adicCompletionIntegers E := by
  let M : Matrix (Fin n) (Fin n) (w.adicCompletionIntegers E) := Matrix.of fun i j => ⟨A i j, hA i j⟩
  have hMA : M.map (w.adicCompletionIntegers E).subtype = A := by ext i j; rfl
  refine ⟨fun k => ?_, ?_⟩
  · rw [← hMA, Matrix.charpoly_map, Polynomial.coeff_map]
    exact (M.charpoly.coeff k).2
  · have hdet : A.det = ((M.det : w.adicCompletionIntegers E) : w.adicCompletion E) := by
      rw [← hMA]; exact (RingHom.map_det (w.adicCompletionIntegers E).subtype M).symm
    rw [hdet]; exact M.det.2

theorem entries_int_of_mem_KGL {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ)
    (g : GL (Fin n) (w.adicCompletion E)) (hg : g ∈ GlobalTheory.LFun.KGL w n) :
    (∀ i j, g.1 i j ∈ w.adicCompletionIntegers E) ∧ ∀ i j, (g⁻¹).1 i j ∈ w.adicCompletionIntegers E := by
  simp only [GlobalTheory.LFun.KGL] at hg
  unfold GLint at hg
  obtain ⟨h, rfl⟩ := hg
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · have : (bc (Ov E w).subtype h).1 i j = ((h.1 i j : Ov E w) : w.adicCompletion E) := rfl
    rw [this]; exact (h.1 i j).2
  · have : ((bc (Ov E w).subtype h)⁻¹).1 i j = (((h⁻¹).1 i j : Ov E w) : w.adicCompletion E) := by
      rw [← map_inv]; rfl
    rw [this]; exact ((h⁻¹).1 i j).2

theorem kint : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E) (g : GLw n w),
    g ∈ GlobalTheory.LFun.KGL w n →
    (∀ k, Valued.v (g.val.charpoly.coeff k) ≤ 1) ∧ Valued.v (g.val.charpoly.coeff 0) = 1 := by
  intro E _ _ _ n w g hg
  obtain ⟨h1, h2⟩ := entries_int_of_mem_KGL w n g hg
  obtain ⟨hc, hd⟩ := charpoly_coeff_det_int w g.val h1
  obtain ⟨-, hd'⟩ := charpoly_coeff_det_int w (g⁻¹).val h2
  rw [HeightOneSpectrum.mem_adicCompletionIntegers] at hd hd'
  refine ⟨fun k => (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (hc k), ?_⟩
  have hprod : g.val.det * (g⁻¹).val.det = 1 := by
    rw [← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one]
  have hv : Valued.v g.val.det * Valued.v (g⁻¹).val.det = 1 := by rw [← map_mul, hprod, map_one]
  have hdet : Valued.v g.val.det = 1 := by
    refine le_antisymm hd ?_
    calc (1 : _) = Valued.v g.val.det * Valued.v (g⁻¹).val.det := hv.symm
      _ ≤ Valued.v g.val.det * 1 := mul_le_mul' le_rfl hd'
      _ = Valued.v g.val.det := mul_one _
  have h0 : g.val.charpoly.coeff 0 = (-1) ^ Fintype.card (Fin n) * g.val.det := by
    rw [Matrix.det_eq_sign_charpoly_coeff, ← mul_assoc, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow, one_mul]
  rw [h0, map_mul, map_pow, Valuation.map_neg, map_one, one_pow, one_mul, hdet]

end GlobalTheory.CharpolyInt
