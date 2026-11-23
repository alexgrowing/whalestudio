import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.Gramlow
import Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.Grampsd

open Matrix
open scoped ComplexOrder

theorem UpperTheory.V.KT.grampd :
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (G : Matrix ι ι ℝ), G.IsHermitian →
    (∀ c : ι → ℤ, c ≠ 0 → 1 ≤ (fun i => (c i : ℝ)) ⬝ᵥ (G *ᵥ fun i => (c i : ℝ))) →
    G.PosDef ∧ 1 ≤ (4 * (Fintype.card ι : ℝ)) ^ Fintype.card ι * G.det := by
  intro ι _ _ G hG hint
  have hpsd : G.PosSemidef := by
    refine UpperTheory.V.KT.grampsd ι G hG (fun c => ?_)
    by_cases hc : c = 0
    · subst hc
      simp
    · exact le_trans zero_le_one (hint c hc)
  have hpert : ∀ ε : ℝ, 0 < ε →
      1 ≤ (4 * (Fintype.card ι : ℝ)) ^ Fintype.card ι * (G + ε • (1 : Matrix ι ι ℝ)).det := by
    intro ε hε
    have hpd : (G + ε • (1 : Matrix ι ι ℝ)).PosDef :=
      Matrix.PosDef.posSemidef_add hpsd (Matrix.PosDef.smul Matrix.PosDef.one hε)
    refine UpperTheory.V.KT.gramlow ι _ hpd (fun c hc => ?_)
    have h1 := hint c hc
    have h2 : 0 ≤ (fun i => (c i : ℝ)) ⬝ᵥ (fun i => (c i : ℝ)) := by
      simp only [dotProduct]
      exact Finset.sum_nonneg (fun i _ => mul_self_nonneg _)
    rw [Matrix.add_mulVec, dotProduct_add, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul,
      smul_eq_mul]
    nlinarith
  have hcont : Continuous fun ε : ℝ =>
      (4 * (Fintype.card ι : ℝ)) ^ Fintype.card ι * (G + ε • (1 : Matrix ι ι ℝ)).det := by
    refine continuous_const.mul (Continuous.matrix_det ?_)
    exact continuous_const.add (continuous_id.smul continuous_const)
  have hdet : 1 ≤ (4 * (Fintype.card ι : ℝ)) ^ Fintype.card ι * G.det := by
    have ht : Filter.Tendsto (fun ε : ℝ =>
        (4 * (Fintype.card ι : ℝ)) ^ Fintype.card ι * (G + ε • (1 : Matrix ι ι ℝ)).det)
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds ((4 * (Fintype.card ι : ℝ)) ^ Fintype.card ι * (G + (0 : ℝ) • (1 : Matrix ι ι ℝ)).det)) :=
      (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
    rw [zero_smul, add_zero] at ht
    refine ge_of_tendsto ht ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact hpert ε hε
  refine ⟨?_, hdet⟩
  rw [hpsd.posDef_iff_isUnit, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
  intro h0
  rw [h0, mul_zero] at hdet
  linarith
