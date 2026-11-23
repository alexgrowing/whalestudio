import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.OrderedConst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationDetBlocks

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType Matrix

namespace GlobalTheory.PsType

theorem conj_blockLower_mem_theta : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (ψ : Fin n → kˣ →* ℂˣ) (r : ℕ) (ϖ : k), ϖ ≠ 0 → valuation k ϖ < 1 → ∀ (z : GL (Fin n) k), z.val = Matrix.diagonal (fun i : Fin n => if (i : ℕ) < r then ϖ else 1) → ∀ g ∈ grp ψ, (∀ a b : Fin n, (a : ℕ) < r → r ≤ (b : ℕ) → g.val a b = 0) → z⁻¹ * g * z ∈ grp ψ ∧ theta ψ (z⁻¹ * g * z) = theta ψ g := by
  intro k _ _ _ _ n ψ r ϖ hϖ hv z hz g hg hup
  set d : Fin n → k := fun i => if (i : ℕ) < r then ϖ else 1 with hd
  have hd0 : ∀ i, d i ≠ 0 := by
    intro i; simp only [hd]; split_ifs <;> simp [hϖ]
  have h2 : diagonal (fun i => (d i)⁻¹) * z.val = 1 := by
    rw [hz, diagonal_mul_diagonal]
    ext i j
    simp [diagonal, one_apply, hd0]
  have hzi : (z⁻¹).val = diagonal (fun i => (d i)⁻¹) := by
    calc (z⁻¹).val = (diagonal (fun i => (d i)⁻¹) * z.val) * (z⁻¹).val := by rw [h2, Matrix.one_mul]
      _ = diagonal (fun i => (d i)⁻¹) := by
        rw [Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
  have hent : ∀ i j, (z⁻¹ * g * z).val i j = (d i)⁻¹ * g.val i j * d j := by
    intro i j
    rw [Units.val_mul, Units.val_mul, hzi, hz, mul_diagonal, diagonal_mul]
  have hupper : ∀ i j : Fin n, i < j → (z⁻¹ * g * z).val i j = g.val i j := by
    intro i j hij
    rw [hent]
    have hij' : (i : ℕ) < j := hij
    by_cases hi : (i : ℕ) < r
    · by_cases hj : (j : ℕ) < r
      · simp only [hd, if_pos hi, if_pos hj]; field_simp
      · rw [hup i j hi (not_lt.1 hj)]; simp
    · have hj : ¬ (j : ℕ) < r := by omega
      simp only [hd, if_neg hi, if_neg hj]; simp
  have hle : ∀ i j, valuation k ((z⁻¹ * g * z).val i j) ≤ valuation k (g.val i j) := by
    intro i j
    rw [hent]
    by_cases hi : (i : ℕ) < r
    · by_cases hj : (j : ℕ) < r
      · simp only [hd, if_pos hi, if_pos hj]
        have : ϖ⁻¹ * g.val i j * ϖ = g.val i j := by field_simp
        rw [this]
      · rw [hup i j hi (not_lt.1 hj)]; simp
    · by_cases hj : (j : ℕ) < r
      · simp only [hd, if_neg hi, if_pos hj, inv_one, one_mul, map_mul]
        calc valuation k (g.val i j) * valuation k ϖ ≤ valuation k (g.val i j) * 1 := by
              gcongr
          _ = _ := mul_one _
      · simp only [hd, if_neg hi, if_neg hj]; simp
  have hdet : (z⁻¹ * g * z).val.det = g.val.det := by
    rw [Units.val_mul, Units.val_mul, det_mul, det_mul, mul_comm, ← mul_assoc, ← det_mul,
      ← Units.val_mul, mul_inv_cancel, Units.val_one, det_one, one_mul]
  have hminor : ∀ m, minor (z⁻¹ * g * z) m = minor g m := by
    intro m
    simp only [minor]
    set G := g.val.toSquareBlockProp (fun i => i ≤ m) with hG
    have e : (z⁻¹ * g * z).val.toSquareBlockProp (fun i => i ≤ m) =
        of fun (i j : {a // a ≤ m}) => (d i)⁻¹ * (of fun (i j : {a // a ≤ m}) => d j * G i j) i j := by
      ext i j
      simp only [hG, toSquareBlockProp_def, toBlock_apply, of_apply, hent]
      ring
    rw [e, det_mul_column (fun i : {a // a ≤ m} => (d i)⁻¹), det_mul_row (fun j : {a // a ≤ m} => d j) G,
      ← mul_assoc, ← Finset.prod_mul_distrib]
    rw [Finset.prod_eq_one (fun (i : {a // a ≤ m}) _ => inv_mul_cancel₀ (hd0 i.1)), one_mul]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · have hgk := (GlobalTheory.LocStd.mem_KO_iff_det.1 hg.1)
    refine GlobalTheory.LocStd.mem_KO_iff_det.2 ⟨fun i j => ?_, by rw [hdet]; exact hgk.2⟩
    exact (Valuation.mem_integer_iff _ _).2 ((hle i j).trans ((Valuation.mem_integer_iff _ _).1 (hgk.1 i j)))
  · intro i j hij
    rw [hupper i j hij]
    exact hg.2 i j hij
  · simp only [theta, hminor]

end GlobalTheory.PsType
