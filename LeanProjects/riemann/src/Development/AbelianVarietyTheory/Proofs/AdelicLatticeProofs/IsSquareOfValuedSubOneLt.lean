import Mathlib
open NumberField IsDedekindDomain
open scoped Matrix WithZero

namespace GlobalTheory.LocalQuad

namespace SquareTheorem

open NumberField IsDedekindDomain in
open scoped Matrix WithZero in

theorem _root_.GlobalTheory.LocalQuad.SquareTheorem.isSquare_of_norm_sub_one_lt {K : Type*} [NormedField K] [CompleteSpace K]
    [IsUltrametricDist K] (x : K) (h : ‖x - 1‖ < ‖(4 : K)‖) : IsSquare x := by
  have h4 : (4 : K) ≠ 0 := norm_pos_iff.1 (lt_of_le_of_lt (norm_nonneg _) h)
  set c : K := (x - 1) / 4 with hc
  have hx : x = 1 + 4 * c := by rw [hc]; field_simp; ring
  have hc1 : ‖c‖ < 1 := by
    rw [hc, norm_div, div_lt_one (norm_pos_iff.2 h4)]; exact h
  set r : ℝ := ‖c‖ with hr
  have hr0 : 0 ≤ r := norm_nonneg _
  have hsq : ∀ z : K, ‖z‖ ≤ r → ‖z ^ 2‖ ≤ r := by
    intro z hz
    rw [norm_pow]
    calc ‖z‖ ^ 2 ≤ r ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hz 2
      _ ≤ r := by nlinarith
  let s := Metric.closedBall (0 : K) r
  haveI : CompleteSpace s := Metric.isClosed_closedBall.completeSpace_coe
  have hmem : ∀ z : s, c - (z : K) ^ 2 ∈ s := by
    intro z
    have hz : ‖(z : K)‖ ≤ r := mem_closedBall_zero_iff.1 z.2
    have hu := IsUltrametricDist.norm_add_le_max c (-((z : K) ^ 2))
    rw [norm_neg, ← sub_eq_add_neg] at hu
    exact mem_closedBall_zero_iff.2 (hu.trans (max_le le_rfl (hsq _ hz)))
  let f : s → s := fun z => ⟨c - (z : K) ^ 2, hmem z⟩
  have hf : ContractingWith ‖c‖₊ f := by
    refine ⟨hc1, LipschitzWith.of_dist_le_mul fun a b => ?_⟩
    have ha : ‖(a : K)‖ ≤ r := mem_closedBall_zero_iff.1 a.2
    have hb : ‖(b : K)‖ ≤ r := mem_closedBall_zero_iff.1 b.2
    rw [Subtype.dist_eq, Subtype.dist_eq, dist_eq_norm, dist_eq_norm]
    have : (c - (a : K) ^ 2) - (c - (b : K) ^ 2) = ((b : K) + a) * ((b : K) - a) := by ring
    simp only [f, this, norm_mul, coe_nnnorm]
    rw [norm_sub_rev (b : K)]
    exact mul_le_mul_of_nonneg_right
      ((IsUltrametricDist.norm_add_le_max _ _).trans (max_le hb ha)) (norm_nonneg _)
  haveI : Nonempty s := ⟨⟨0, by simp [s, hr0]⟩⟩
  set z : s := ContractingWith.fixedPoint f hf
  have hz : (z : K) = c - (z : K) ^ 2 := by
    have := ContractingWith.fixedPoint_isFixedPt (f := f) hf
    exact (congrArg Subtype.val this).symm
  exact ⟨1 + 2 * (z : K), by linear_combination hx - 4 * hz⟩

end SquareTheorem

open NumberField IsDedekindDomain in
open scoped Matrix WithZero in

theorem _root_.GlobalTheory.LocalQuad.isSquare_of_valued_sub_one_lt (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) (x : v.adicCompletion F)
    (h : Valued.v (x - 1) < Valued.v (4 : v.adicCompletion F)) : IsSquare x :=
  _root_.GlobalTheory.LocalQuad.SquareTheorem.isSquare_of_norm_sub_one_lt x (Valued.toNormedField.norm_lt_iff.2 h)

end GlobalTheory.LocalQuad
