import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.CharpolyBound

theorem continuous_coeff {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] (n i : ℕ) :
    Continuous fun M : Matrix (Fin n) (Fin n) K => M.charpoly.coeff i := by
  have h : (fun M : Matrix (Fin n) (Fin n) K => M.charpoly.coeff i) =
      fun M => MvPolynomial.eval (fun ij : Fin n × Fin n => M ij.1 ij.2)
        ((Matrix.charpoly.univ K (Fin n)).coeff i) := by
    funext M
    exact (Matrix.charpoly.univ_coeff_eval₂Hom (Fin n) (RingHom.id K) (fun ij : Fin n × Fin n => M ij.1 ij.2) i).symm
  rw [h]
  refine (MvPolynomial.continuous_eval _).comp ?_
  exact continuous_pi fun ij => (continuous_apply ij.2).comp (continuous_apply ij.1)

variable {E : Type} [Field E] [NumberField E]

theorem isOpen_vle (w : Pl E) (m : ℤ) : IsOpen {y : w.adicCompletion E | Valued.v y ≤ WithZero.exp m} := by
  obtain ⟨c, hc⟩ := HeightOneSpectrum.valuedAdicCompletion_surjective E w (WithZero.exp m)
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [map_zero] at hc
    exact WithZero.exp_ne_zero hc.symm
  have : {y : w.adicCompletion E | Valued.v y ≤ WithZero.exp m} = {y | Valued.v.restrict y ≤ Valued.v.restrict c} := by
    ext y
    simp only [Set.mem_ofPred_eq, Valuation.restrict_le_iff, hc]
  rw [this]
  exact Valued.isOpen_closedBall _ (by simp [hc0])

theorem exists_bound {X : Type} [TopologicalSpace X] (w : Pl E) {f : X → w.adicCompletion E} (hf : Continuous f)
    {C : Set X} (hC : IsCompact C) : ∃ B : WithZero (Multiplicative ℤ), ∀ x ∈ C, Valued.v (f x) ≤ B := by
  have hcov : C ⊆ ⋃ m : ℤ, f ⁻¹' {y | Valued.v y ≤ WithZero.exp m} := by
    intro x _
    simp only [Set.mem_iUnion, Set.mem_preimage, Set.mem_setOf_eq]
    rcases eq_or_ne (Valued.v (f x)) 0 with h | h
    · exact ⟨0, by rw [h]; exact zero_le'⟩
    · exact ⟨WithZero.log (Valued.v (f x)), (WithZero.exp_log h).ge⟩
  have hmono : Monotone fun m : ℤ => f ⁻¹' {y | Valued.v y ≤ WithZero.exp m} := by
    intro a b hab x hx
    exact le_trans hx (WithZero.exp_le_exp.2 hab)
  obtain ⟨m, hm⟩ := hC.elim_directed_cover _ (fun m => (isOpen_vle w m).preimage hf) hcov hmono.directed_le
  exact ⟨WithZero.exp m, fun x hx => hm hx⟩

end GlobalTheory.CharpolyBound

open GlobalTheory.CharpolyBound in
theorem GlobalTheory.CharpolyBound.bound : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E) (C : Set (GLw n w)), IsCompact C → ∃ B : WithZero (Multiplicative ℤ), ∀ g ∈ C, (∀ k, Valued.v (g.val.charpoly.coeff k) ≤ B) ∧ Valued.v ((g.val.charpoly.coeff 0)⁻¹) ≤ B := by
  intro E _ _ _ n w C hC
  have hval : Continuous fun g : GLw n w => g.val := Units.continuous_val
  have hinv : Continuous fun g : GLw n w => ((g⁻¹ : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) :=
    Units.continuous_coe_inv
  have hk : ∀ k : ℕ, ∃ B : WithZero (Multiplicative ℤ), ∀ g ∈ C, Valued.v (g.val.charpoly.coeff k) ≤ B :=
    fun k => exists_bound w ((continuous_coeff n k).comp hval) hC
  choose Bk hBk using hk
  obtain ⟨Bi, hBi⟩ := exists_bound w (hinv.matrix_det) hC
  refine ⟨(Finset.range (n + 1)).sup Bk ⊔ Bi, fun g hg => ⟨fun k => ?_, ?_⟩⟩
  · by_cases hkn : k ≤ n
    · exact le_sup_of_le_left ((hBk k g hg).trans (Finset.le_sup (f := Bk) (Finset.mem_range.2 (by omega))))
    · rw [coeff_eq_zero_of_natDegree_lt (by rw [charpoly_natDegree_eq_dim, Fintype.card_fin]; omega), map_zero]
      exact zero_le'
  · have h0 : g.val.charpoly.coeff 0 = (-1) ^ n * g.val.det := by
      rw [det_eq_sign_charpoly_coeff, Fintype.card_fin, ← mul_assoc, ← pow_add, ← two_mul, pow_mul]
      simp
    have hdet : g.val.det * ((g⁻¹ : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)).det = 1 := by
      rw [← det_mul, Units.mul_inv, det_one]
    have hc : (g.val.charpoly.coeff 0)⁻¹ =
        (-1) ^ n * ((g⁻¹ : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)).det := by
      rw [h0, mul_inv, inv_eq_of_mul_eq_one_right hdet, ← inv_pow, inv_neg_one]
    rw [hc, map_mul, map_pow, Valuation.map_neg, map_one, one_pow, one_mul]
    exact le_sup_of_le_right (hBi g hg)
