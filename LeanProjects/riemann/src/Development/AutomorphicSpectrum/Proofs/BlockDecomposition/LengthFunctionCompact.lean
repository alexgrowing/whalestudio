import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GelfandFlags.IntSmooth

noncomputable section

open Matrix Finset

namespace GlobalTheory.CompanionTheory.LgBound

open PositivityTheory.RgBcC
open PositivityTheory.RgTw (Mat G)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem lgCpt : PositivityTheory.RgBcC.VC.LgCpt := by
  intro n R
  haveI : ProperSpace (Mat n) := FiniteDimensional.proper ℂ _
  let f : G n → ℝ := fun y => 1 + ∑ a, ∑ b, (‖y.val a b‖ ^ 2 + ‖(y⁻¹).val a b‖ ^ 2)
  have hinv : ∀ y : G n, (y.val)⁻¹ = (y⁻¹).val := fun y => (Matrix.coe_units_inv y).symm
  have hc1 : Continuous fun y : G n => y.val := Units.continuous_val
  have hc2 : Continuous fun y : G n => (y⁻¹).val := Units.continuous_val.comp continuous_inv
  have hfc : Continuous f := by
    refine continuous_const.add (continuous_finset_sum _ fun a _ => continuous_finset_sum _ fun b _ => ?_)
    exact ((hc1.matrix_elem a b).norm.pow 2).add ((hc2.matrix_elem a b).norm.pow 2)
  have hsum : ∀ y : G n, 0 ≤ ∑ a, ∑ b, (‖y.val a b‖ ^ 2 + ‖(y⁻¹).val a b‖ ^ 2) := fun y =>
    Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => by positivity
  have hfpos : ∀ y, 0 < f y := fun y => by
    have := hsum y
    show 0 < 1 + _
    linarith
  have hS : {y : G n | lg y.val ≤ R} = f ⁻¹' Set.Iic (Real.exp R) := by
    ext y
    simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_Iic, lg, hinv]
    exact Real.log_le_iff_le_exp (hfpos y)
  rw [hS]
  have hclosed : IsClosed (f ⁻¹' Set.Iic (Real.exp R)) := isClosed_Iic.preimage hfc

  set r : ℝ := Real.exp R with hr
  have hr0 : 0 ≤ r + 1 := by positivity
  have hterm : ∀ y : G n, f y ≤ r → ∀ a b, ‖y.val a b‖ ^ 2 + ‖(y⁻¹).val a b‖ ^ 2 ≤ r := by
    intro y hy a b
    have h1 : ‖y.val a b‖ ^ 2 + ‖(y⁻¹).val a b‖ ^ 2 ≤ ∑ b, (‖y.val a b‖ ^ 2 + ‖(y⁻¹).val a b‖ ^ 2) :=
      Finset.single_le_sum (f := fun b => ‖y.val a b‖ ^ 2 + ‖(y⁻¹).val a b‖ ^ 2)
        (fun b _ => by positivity) (Finset.mem_univ b)
    have h2 : ∑ b, (‖y.val a b‖ ^ 2 + ‖(y⁻¹).val a b‖ ^ 2) ≤ ∑ a, ∑ b, (‖y.val a b‖ ^ 2 + ‖(y⁻¹).val a b‖ ^ 2) :=
      Finset.single_le_sum (f := fun a => ∑ b, (‖y.val a b‖ ^ 2 + ‖(y⁻¹).val a b‖ ^ 2))
        (fun a _ => Finset.sum_nonneg fun b _ => by positivity) (Finset.mem_univ a)
    have h3 : 1 + ∑ a, ∑ b, (‖y.val a b‖ ^ 2 + ‖(y⁻¹).val a b‖ ^ 2) ≤ r := hy
    linarith
  have hle : ∀ t : ℝ, 0 ≤ t → t ^ 2 ≤ r → t ≤ r + 1 := by
    intro t ht h
    nlinarith [sq_nonneg (t - 1)]
  have hb1 : ∀ y : G n, f y ≤ r → ‖y.val‖ ≤ r + 1 := by
    intro y hy
    refine (Matrix.norm_le_iff hr0).2 fun a b => hle _ (norm_nonneg _) ?_
    have := hterm y hy a b
    have h2 : 0 ≤ ‖(y⁻¹).val a b‖ ^ 2 := by positivity
    linarith
  have hb2 : ∀ y : G n, f y ≤ r → ‖(y⁻¹).val‖ ≤ r + 1 := by
    intro y hy
    refine (Matrix.norm_le_iff hr0).2 fun a b => hle _ (norm_nonneg _) ?_
    have := hterm y hy a b
    have h2 : 0 ≤ ‖y.val a b‖ ^ 2 := by positivity
    linarith
  have hball : IsCompact (Metric.closedBall (0 : Mat n) (r + 1)) := isCompact_closedBall _ _
  have hK : IsCompact ((fun p : Mat n × Mat n => (p.1, MulOpposite.op p.2)) ''
      (Metric.closedBall (0 : Mat n) (r + 1) ×ˢ Metric.closedBall (0 : Mat n) (r + 1))) :=
    (hball.prod hball).image (continuous_fst.prodMk (MulOpposite.continuous_op.comp continuous_snd))
  have hpre := (Units.isClosedEmbedding_embedProduct (α := Mat n)).isCompact_preimage hK
  refine hpre.of_isClosed_subset hclosed ?_
  intro y hy
  refine ⟨(y.val, (y⁻¹).val), ⟨?_, ?_⟩, rfl⟩
  · simpa using hb1 y hy
  · simpa using hb2 y hy

end GlobalTheory.CompanionTheory.LgBound
