import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DwCons
open MeasureTheory Matrix Finset
open scoped ContDiff
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.SobGL
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

noncomputable section

namespace GlobalTheory.CompanionTheory.SobGL

def lgArg {n : ℕ} (p : Mat n × Mat n) : ℝ :=
  1 + ∑ a, ∑ b, (‖p.1 a b‖ ^ 2 + ‖p.2 a b‖ ^ 2)

theorem lgArg_continuous {n : ℕ} : Continuous (lgArg (n := n)) := by
  unfold lgArg
  refine continuous_const.add (continuous_finset_sum _ fun a _ => continuous_finset_sum _ fun b _ => ?_)
  have h1 : Continuous fun p : Mat n × Mat n => p.1 a b :=
    (continuous_id.matrix_elem a b).comp continuous_fst
  have h2 : Continuous fun p : Mat n × Mat n => p.2 a b :=
    (continuous_id.matrix_elem a b).comp continuous_snd
  exact (h1.norm.pow 2).add (h2.norm.pow 2)

theorem one_le_lgArg {n : ℕ} (p : Mat n × Mat n) : 1 ≤ lgArg p := by
  unfold lgArg
  have : 0 ≤ ∑ a, ∑ b, (‖p.1 a b‖ ^ 2 + ‖p.2 a b‖ ^ 2) :=
    Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => by positivity
  linarith

theorem entry_sq_le_lgArg {n : ℕ} (p : Mat n × Mat n) (a b : Fin n) :
    ‖p.1 a b‖ ^ 2 + ‖p.2 a b‖ ^ 2 ≤ lgArg p := by
  unfold lgArg
  have h1 : ‖p.1 a b‖ ^ 2 + ‖p.2 a b‖ ^ 2 ≤ ∑ b, (‖p.1 a b‖ ^ 2 + ‖p.2 a b‖ ^ 2) :=
    Finset.single_le_sum (f := fun b => ‖p.1 a b‖ ^ 2 + ‖p.2 a b‖ ^ 2)
      (fun b _ => by positivity) (Finset.mem_univ b)
  have h2 : ∑ b, (‖p.1 a b‖ ^ 2 + ‖p.2 a b‖ ^ 2) ≤ ∑ a, ∑ b, (‖p.1 a b‖ ^ 2 + ‖p.2 a b‖ ^ 2) :=
    Finset.single_le_sum (f := fun a => ∑ b, (‖p.1 a b‖ ^ 2 + ‖p.2 a b‖ ^ 2))
      (fun a _ => Finset.sum_nonneg fun b _ => by positivity) (Finset.mem_univ a)
  linarith

theorem lg_eq_log_lgArg {n : ℕ} (y : Mat n) : lg y = Real.log (lgArg (y, y⁻¹)) := rfl

theorem continuousOn_matInv {n : ℕ} : ContinuousOn (fun y : Mat n => y⁻¹) (GLs n) := by
  have hdet : ContinuousOn (fun y : Mat n => (y.det)⁻¹) (GLs n) :=
    (continuous_id.matrix_det).continuousOn.inv₀ fun y hy => hy
  have hadj : Continuous fun y : Mat n => y.adjugate := continuous_id.matrix_adjugate
  have : (fun y : Mat n => y⁻¹) = fun y => (y.det)⁻¹ • y.adjugate := by
    funext y
    rw [Matrix.inv_def, Ring.inverse_eq_inv']
  rw [this]
  exact hdet.smul hadj.continuousOn

theorem continuousOn_lg {n : ℕ} : ContinuousOn (lg (n := n)) (GLs n) := by
  have hp : ContinuousOn (fun y : Mat n => (y, y⁻¹)) (GLs n) :=
    continuousOn_id.prodMk continuousOn_matInv
  have h := lgArg_continuous.comp_continuousOn hp
  exact ContinuousOn.log h fun y _ => (lt_of_lt_of_le one_pos (one_le_lgArg (y, y⁻¹))).ne'

def pairOf {n : ℕ} (y : G n) : Mat n × Mat n := (y.val, (y⁻¹ : G n).val)

theorem pairOf_isInducing {n : ℕ} : Topology.IsInducing (pairOf (n := n)) := by
  have h := (Units.isEmbedding_embedProduct (M := Mat n)).isInducing
  have h2 : Topology.IsInducing (fun p : Mat n × (Mat n)ᵐᵒᵖ => (p.1, p.2.unop)) :=
    ((Homeomorph.refl (Mat n)).prodCongr MulOpposite.opHomeomorph.symm).isInducing
  exact h2.comp h

theorem isCompact_entryBox {n : ℕ} (r : ℝ) : IsCompact {m : Mat n | ∀ a b, ‖m a b‖ ≤ r} := by
  have h : IsCompact (Set.pi Set.univ fun _ : Fin n =>
      Set.pi Set.univ fun _ : Fin n => Metric.closedBall (0 : ℂ) r) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _
  have e : {m : Fin n → Fin n → ℂ | ∀ a b, ‖m a b‖ ≤ r} = Set.pi Set.univ fun _ : Fin n =>
      Set.pi Set.univ fun _ : Fin n => Metric.closedBall (0 : ℂ) r := by
    ext m
    simp [Set.mem_pi]
  have h' : IsCompact {m : Fin n → Fin n → ℂ | ∀ a b, ‖m a b‖ ≤ r} := e ▸ h
  exact h'

theorem isCompact_lg_le {n : ℕ} (R : ℝ) : IsCompact {y : G n | lg y.val ≤ R} := by
  rw [pairOf_isInducing.isCompact_iff]
  have hset : pairOf '' {y : G n | lg y.val ≤ R} =
      {p : Mat n × Mat n | p.1 * p.2 = 1 ∧ p.2 * p.1 = 1 ∧ lgArg p ≤ Real.exp R} := by
    ext p
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨by simp [pairOf], by simp [pairOf], ?_⟩
      have hinv : (y⁻¹ : G n).val = y.val⁻¹ := Matrix.coe_units_inv y
      have hy' : Real.log (lgArg (pairOf y)) ≤ R := by
        have : lg y.val = Real.log (lgArg (pairOf y)) := by
          rw [lg_eq_log_lgArg, pairOf, hinv]
        rw [← this]; exact hy
      have hpos : 0 < lgArg (pairOf y) := lt_of_lt_of_le one_pos (one_le_lgArg _)
      exact (Real.log_le_iff_le_exp hpos).1 hy'
    · rintro ⟨h1, h2, h3⟩
      refine ⟨⟨p.1, p.2, h1, h2⟩, ?_, ?_⟩
      · set y : G n := ⟨p.1, p.2, h1, h2⟩ with hy
        have hinv : (y⁻¹ : G n).val = y.val⁻¹ := Matrix.coe_units_inv y
        have hpy : pairOf y = p := rfl
        have : lg y.val = Real.log (lgArg p) := by
          rw [lg_eq_log_lgArg, ← hinv, ← hpy]; rfl
        have hpos : 0 < lgArg p := lt_of_lt_of_le one_pos (one_le_lgArg _)
        show lg y.val ≤ R
        rw [this]
        exact (Real.log_le_iff_le_exp hpos).2 h3
      · rfl
  rw [hset]
  have hbox : IsCompact ({m : Mat n | ∀ a b, ‖m a b‖ ≤ Real.sqrt (Real.exp R)} ×ˢ
      {m : Mat n | ∀ a b, ‖m a b‖ ≤ Real.sqrt (Real.exp R)}) :=
    (isCompact_entryBox _).prod (isCompact_entryBox _)
  refine hbox.of_isClosed_subset ?_ ?_
  · have c1 : IsClosed {p : Mat n × Mat n | p.1 * p.2 = 1} :=
      isClosed_eq (continuous_fst.matrix_mul continuous_snd) continuous_const
    have c2 : IsClosed {p : Mat n × Mat n | p.2 * p.1 = 1} :=
      isClosed_eq (continuous_snd.matrix_mul continuous_fst) continuous_const
    have c3 : IsClosed {p : Mat n × Mat n | lgArg p ≤ Real.exp R} :=
      isClosed_le lgArg_continuous continuous_const
    exact c1.inter (c2.inter c3)
  · rintro p ⟨-, -, h3⟩
    have hb : ∀ a b, ‖p.1 a b‖ ^ 2 + ‖p.2 a b‖ ^ 2 ≤ Real.exp R := fun a b =>
      (entry_sq_le_lgArg p a b).trans h3
    refine ⟨fun a b => Real.le_sqrt_of_sq_le ?_, fun a b => Real.le_sqrt_of_sq_le ?_⟩
    · have := hb a b; nlinarith [sq_nonneg ‖p.2 a b‖]
    · have := hb a b; nlinarith [sq_nonneg ‖p.1 a b‖]

theorem lg_continuousOn_and_isCompact :
    ∀ n : ℕ, ContinuousOn (lg (n := n)) (GLs n) ∧ ∀ R : ℝ, IsCompact {y : G n | lg y.val ≤ R} :=
  fun _ => ⟨continuousOn_lg, isCompact_lg_le⟩

end GlobalTheory.CompanionTheory.SobGL
