import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SecJets4
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.MatrixLemma
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.PosSemidefOfForallCombination
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.InhabSt

open NumberField MeasureTheory ReciprocityTheory.GeometryOfNumbersTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LieHt
open scoped ComplexOrder

namespace GlobalTheory

open Matrix in

theorem det_mul_det_le_of_fromBlocks_sub_posSemidef {m k : Type*} [Fintype m] [DecidableEq m]
    [Fintype k] [DecidableEq k] {A : Matrix m m ℂ} {X : Matrix m k ℂ} {Y : Matrix k m ℂ}
    {D B : Matrix k k ℂ} (hA : A.PosDef) (hB : B.PosDef)
    (h : (fromBlocks A X Y (D - B)).PosSemidef) :
    A.det.re * B.det.re ≤ (fromBlocks A X Y D).det.re := by
  have hY : Y = Xᴴ := (isHermitian_fromBlocks_iff.mp h.1).2.1.symm
  subst hY
  have : Invertible A := hA.isUnit.invertible
  have hS : (D - B - Xᴴ * A⁻¹ * X).PosSemidef := (PosDef.fromBlocks₁₁ X (D - B) hA).mp h
  have hdet : (fromBlocks A X Xᴴ D).det = A.det * (D - Xᴴ * A⁻¹ * X).det := by
    rw [det_fromBlocks₁₁, invOf_eq_nonsing_inv]
  have hS' : (D - Xᴴ * A⁻¹ * X - B).PosSemidef := by
    rwa [sub_right_comm]
  have hmono := gramSt_det_re_le_of_sub hB hS'
  obtain ⟨hAre, hAim⟩ := Complex.pos_iff.mp hA.det_pos
  rw [hdet, Complex.mul_re, ← hAim, zero_mul, sub_zero]
  exact mul_le_mul_of_nonneg_left hmono hAre.le

open Matrix in

theorem log_det_gram_add_le_of_adapted_frame (K : Type) [Field K] [NumberField K] (m m' : ℕ)
    (h : HermFam K (Fin m → K)) (h' : HermFam K (Fin m' → K))
    (q : (Fin m → K) →ₗ[K] (Fin m' → K)) (C : ℝ) (hC : 0 < C) (σ : K →+* ℂ) (s t : ℕ)
    (a : Fin s → Fin m → K) (b : Fin t → Fin m → K)
    (hab : LinearIndependent K (Fin.append a b)) (hqb : LinearIndependent K (q ∘ b))
    (hqa : ∀ i, q (a i) = 0)
    (hpsd : ((C : ℂ) • h.gram σ (Fin.append a b) -
      h'.gram σ (q ∘ Fin.append a b)).PosSemidef) :
    Real.log (h.gram σ a).det.re + Real.log (h'.gram σ (q ∘ b)).det.re ≤
      Real.log (h.gram σ (Fin.append a b)).det.re + t * Real.log C := by
  have ha : LinearIndependent K a := by
    have := hab.comp (Fin.castAdd t) (Fin.castAdd_injective s t)
    have e : Fin.append a b ∘ Fin.castAdd t = a := by funext i; simp
    rwa [e] at this
  have hA : (h.gram σ a).PosDef := h.posDef σ _ _ ha
  have hM : (h.gram σ (Fin.append a b)).PosDef := h.posDef σ _ _ hab
  have hB : (h'.gram σ (q ∘ b)).PosDef := h'.posDef σ _ _ hqb
  have hz : ∀ x, h'.form σ x 0 = 0 := fun x => by
    simpa using h'.smul_right σ 0 x 0
  have hz' : ∀ x, h'.form σ 0 x = 0 := fun x => by
    rw [← h'.conj_symm, hz, map_zero]
  have hCc : (0 : ℂ) < (C : ℂ) := by exact_mod_cast hC
  set N := (C : ℂ) • h.gram σ (Fin.append a b) with hN
  have hE : N.submatrix finSumFinEquiv finSumFinEquiv =
      fromBlocks ((C : ℂ) • h.gram σ a) (N.submatrix (Fin.castAdd t) (Fin.natAdd s))
        (N.submatrix (Fin.natAdd s) (Fin.castAdd t))
        (N.submatrix (Fin.natAdd s) (Fin.natAdd s)) := by
    ext (i | i) (j | j) <;> simp [hN, HermFam.gram]
  have hE' : (N - h'.gram σ (q ∘ Fin.append a b)).submatrix finSumFinEquiv finSumFinEquiv =
      fromBlocks ((C : ℂ) • h.gram σ a) (N.submatrix (Fin.castAdd t) (Fin.natAdd s))
        (N.submatrix (Fin.natAdd s) (Fin.castAdd t))
        (N.submatrix (Fin.natAdd s) (Fin.natAdd s) - h'.gram σ (q ∘ b)) := by
    ext (i | i) (j | j) <;> simp [hN, HermFam.gram, hqa, hz, hz']
  have hP := hpsd.submatrix (finSumFinEquiv : Fin s ⊕ Fin t → Fin (s + t))
  rw [hE'] at hP
  have key := det_mul_det_le_of_fromBlocks_sub_posSemidef (hA.smul hCc) hB hP
  rw [← hE, det_submatrix_equiv_self, hN, det_smul, det_smul, Fintype.card_fin, Fintype.card_fin,
    ← Complex.ofReal_pow, ← Complex.ofReal_pow, Complex.re_ofReal_mul, Complex.re_ofReal_mul,
    pow_add] at key
  have pA := (posDef_det_re_pos hA).1
  have pB := (posDef_det_re_pos hB).1
  have pM := (posDef_det_re_pos hM).1
  have key2 : (h.gram σ a).det.re * (h'.gram σ (q ∘ b)).det.re ≤
      (h.gram σ (Fin.append a b)).det.re * C ^ t := by
    refine le_of_mul_le_mul_left ?_ (pow_pos hC s)
    calc _ = C ^ s * (h.gram σ a).det.re * (h'.gram σ (q ∘ b)).det.re := by ring
      _ ≤ _ := key
      _ = _ := by ring
  rw [← Real.log_mul pA.ne' pB.ne', ← Real.log_pow, ← Real.log_mul pM.ne' (pow_pos hC t).ne']
  exact Real.log_le_log (mul_pos pA pB) key2

end GlobalTheory
