import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.SelmerRankBounds.EllipticityFromProductFormula
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AdelicNormVecMulGeOfHeight
open MeasureTheory NumberField IsDedekindDomain Polynomial
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Global GroundTheory.Global.SemiLocal
open GroundTheory.Global.AdeleBaseChange
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Loc PositivityTheory.Rg.Tf.Geo
open scoped ENNReal NumberField.AdeleRing TensorProduct

theorem UpperTheory.exists_compact_fundamental_set_of_height_le :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (R : ℝ), ∃ C : Set (G1 K n), IsCompact C ∧
        ∀ x : G1 K n, qht x ≤ R → ∃ g ∈ Gam K n, ∃ y ∈ C, x = g * y := by
  intro K _ _ n R
  obtain ⟨c, N, hc, h⟩ := UpperTheory.adelicNorm_vecMul_ge_of_height K n
  have hR : 0 < max 1 R + 1 := by positivity
  obtain ⟨C, hC, hC'⟩ := Reduction.exists_isCompact_forall_of_pos_le_height (K := K) (n := n)
    (ε := (c * (max 1 R + 1) ^ N)⁻¹) (by positivity)
  refine ⟨Subtype.val ⁻¹' C, isClosed_normOneGL.isClosedEmbedding_subtypeVal.isCompact_preimage hC, fun x hx => ?_⟩
  obtain ⟨γ, hγ⟩ := exists_lt_of_ciInf_lt (hx.trans_lt ((le_max_right 1 R).trans_lt (lt_add_one _)))
  obtain ⟨δ, hδ, y, hy, e⟩ := hC' ((γ : G1 K n) * x : G1 K n) ((γ : G1 K n) * x).2 fun v hv => by
      rw [inv_le_iff_one_le_mul₀' (by positivity)]
      have h0 := h ((γ : G1 K n) * x : G1 K n) v hv
      have hq := AutomorphicForm.height_pos (K := K) ((γ : G1 K n) * x : G1 K n).1
      have hp : 0 ≤ Reduction.height ((γ : G1 K n) * x : G1 K n).1 v := by
        by_contra hn
        have : 0 ≤ c * AutomorphicForm.height (K := K) ((γ : G1 K n) * x : G1 K n).1 ^ N := by
          positivity
        nlinarith [not_le.1 hn]
      exact h0.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ hq.le hγ.le N) hc.le) hp)
  let d : G1 K n := ⟨δ, rationalGL_le_normOneGL hδ⟩
  have hd : d ∈ Gam K n := hδ
  refine ⟨(γ : G1 K n)⁻¹ * d, mul_mem (inv_mem γ.2) hd, d⁻¹ * ((γ : G1 K n) * x), ?_, by group⟩
  have e' : δ * y = ((γ : G1 K n) * x : G1 K n).1 := e
  change δ⁻¹ * ((γ : G1 K n) * x : G1 K n).1 ∈ C
  rw [← e', inv_mul_cancel_left]
  exact hy
