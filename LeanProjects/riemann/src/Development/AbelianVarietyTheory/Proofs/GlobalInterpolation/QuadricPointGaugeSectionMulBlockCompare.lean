import Mathlib
import Formalism.LocalRingCardinality.DataCD
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.PerpendicularEmbedding
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ContinuousMatrixEntryAbsSum

open MeasureTheory Matrix Filter Topology Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding GlobalTheory.CompactDualQuot
open scoped ENNReal NNReal

namespace GlobalTheory.SectionGaugeCompare

variable {P Q P' Q' : ℕ}

open MeasureTheory Matrix Filter Topology in
open scoped ENNReal NNReal in
variable {P Q P' Q' : ℕ} in
private lemma sum_eq_apply_none_add_sum_some_of_option_equiv {α ι M : Type*} [Fintype α] [Fintype ι]
    [AddCommMonoid M] (e : Option α ≃ ι) (f : ι → M) :
    ∑ k, f k = f (e none) + ∑ b, f (e (some b)) := by
  rw [← Equiv.sum_comp e f, Fintype.sum_option]

open MeasureTheory Matrix Filter Topology in
open scoped ENNReal NNReal in
variable {P Q P' Q' : ℕ} in
private lemma sum_norm_sum_mul_matrix_le_mul_sum_norm_of_norm_le {α : Type*} [Fintype α] (u : α → ℂ)
    (Y : Matrix α α ℂ) (K : ℝ) (hu : ∀ c, ‖u c‖ ≤ K) :
    ∑ b, ‖∑ c, u c * Y c b‖ ≤ K * ∑ c, ∑ b, ‖Y c b‖ := by
  calc ∑ b, ‖∑ c, u c * Y c b‖ ≤ ∑ b, ∑ c, K * ‖Y c b‖ := by
        refine Finset.sum_le_sum fun b _ =>
          (norm_sum_le _ _).trans (Finset.sum_le_sum fun c _ => ?_)
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right (hu c) (norm_nonneg _)
    _ = K * ∑ c, ∑ b, ‖Y c b‖ := by
        rw [Finset.sum_comm, Finset.mul_sum]
        simp_rw [Finset.mul_sum]

open MeasureTheory Matrix Filter Topology in
open scoped ENNReal NNReal in
variable {P Q P' Q' : ℕ} in

theorem _root_.GlobalTheory.SectionGaugeCompare.gauge_section_mul_block : ∀ (P Q P' Q' : ℕ)
    (e : Option (Fin P' ⊕ Fin Q') ≃ (Fin P ⊕ Fin Q)) (j : _root_.Formalism.BasicNotions.UpqT P' Q' → _root_.Formalism.BasicNotions.UpqT P Q),
    _root_.GlobalTheory.CompactDualQuot.IsBlockEmb e j → ∀ t : ℝ, 1 < t → ∃ δ : ℝ, 0 < δ ∧
      ∀ (y : _root_.GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding.Sp P Q) (a : _root_.Formalism.BasicNotions.UpqT P Q), _root_.GlobalTheory.CompactDualQuot.ptGauge e y < δ →
        _root_.GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding.act a (_root_.GlobalTheory.CompactDualQuot.baseVec e) = y →
        (∀ b, ‖_root_.Formalism.BasicNotions.UpqT.mat a (e none) (e (some b))‖ = ‖y (e (some b))‖) →
        (∀ i b, ‖(_root_.Formalism.BasicNotions.UpqT.mat a - 1) (e (some i)) (e (some b))‖ =
          ‖y (e (some i))‖ * ‖y (e (some b))‖ / ‖1 + y (e none)‖) →
        ∀ g : _root_.Formalism.BasicNotions.UpqT P' Q', _root_.GlobalTheory.CompactDualQuot.ptGauge e y + _root_.GlobalTheory.CompactDualQuot.gauge g ≤
            t * _root_.GlobalTheory.CompactDualQuot.gauge (a * j g) ∧
          _root_.GlobalTheory.CompactDualQuot.gauge (a * j g) ≤
            t * (_root_.GlobalTheory.CompactDualQuot.ptGauge e y + _root_.GlobalTheory.CompactDualQuot.gauge g) := by
  intro P Q P' Q' e j hj t ht
  have ht0 : 0 < t := by linarith
  refine ⟨min 1 ((t - 1) / t), lt_min one_pos (div_pos (by linarith) ht0), ?_⟩
  intro y a hy hact hrow hblk g
  unfold _root_.GlobalTheory.CompactDualQuot.IsBlockEmb at hj
  obtain ⟨h00, h0b, hc0, hcb⟩ := hj g
  set A := a.mat with hA
  set D : Matrix (Fin P' ⊕ Fin Q') (Fin P' ⊕ Fin Q') ℂ := g.mat - 1 with hD
  set S : ℝ := ∑ i, ‖y (e (some i))‖ with hS
  set G : ℝ := ∑ c, ∑ b, ‖D c b‖ with hG
  set N : ℝ := ‖y (e none) - 1‖ with hN
  have hgD : g.mat = 1 + D := by rw [hD, add_sub_cancel]
  have hcol : ∀ k, A k (e none) = y k := by
    intro k
    rw [← hact]
    simp [_root_.GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding.act, _root_.GlobalTheory.CompactDualQuot.baseVec, hA, Matrix.mulVec,
      dotProduct, Pi.single_apply]
  have hpt : _root_.GlobalTheory.CompactDualQuot.ptGauge e y = N + 2 * S := by
    unfold _root_.GlobalTheory.CompactDualQuot.ptGauge; rfl
  have hgg : _root_.GlobalTheory.CompactDualQuot.gauge g = G := by
    unfold _root_.GlobalTheory.CompactDualQuot.gauge _root_.GlobalTheory.CompactDualQuot.l1; rfl
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hG0 : 0 ≤ G := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hN0 : 0 ≤ N := norm_nonneg _
  have hyS : ∀ c, ‖y (e (some c))‖ ≤ S := fun c =>
    Finset.single_le_sum (f := fun i => ‖y (e (some i))‖) (fun _ _ => norm_nonneg _)
      (Finset.mem_univ c)
  rw [hpt] at hy
  have hy1 : N + 2 * S < 1 := hy.trans_le (min_le_left _ _)
  have hyt : N + 2 * S < (t - 1) / t := hy.trans_le (min_le_right _ _)
  have hts : 2 * t * S ≤ t - 1 := by
    have := (lt_div_iff₀ ht0).1 hyt
    nlinarith
  have hS1 : S ≤ 1 / 2 := by linarith
  have hc1 : 1 ≤ ‖1 + y (e none)‖ := by
    have h2 : (2 : ℂ) = (1 + y (e none)) - (y (e none) - 1) := by ring
    have := norm_sub_le (1 + y (e none)) (y (e none) - 1)
    rw [← h2] at this
    norm_num at this
    linarith
  set E : Matrix (Fin P' ⊕ Fin Q') (Fin P' ⊕ Fin Q') ℂ :=
    Matrix.of fun i c => (A - 1) (e (some i)) (e (some c)) with hE
  have hEn : ∀ i c, ‖E i c‖ ≤ ‖y (e (some i))‖ * ‖y (e (some c))‖ := by
    intro i c
    have hEic : E i c = (A - 1) (e (some i)) (e (some c)) := rfl
    rw [hEic, hblk i c]
    exact div_le_self (by positivity) hc1
  have hAE : ∀ i c, A (e (some i)) (e (some c)) = (1 + E) i c := by
    intro i c
    simp only [hE, Matrix.add_apply, Matrix.of_apply, Matrix.sub_apply, Matrix.one_apply,
      EmbeddingLike.apply_eq_iff_eq, Option.some.injEq]
    ring
  have hM0 : ∀ k, (a * j g).mat k (e none) = y k := by
    intro k
    show (A * (j g).mat) k (e none) = y k
    rw [Matrix.mul_apply, sum_eq_apply_none_add_sum_some_of_option_equiv e]
    simp [h00, hc0, hcol]
  have hMb : ∀ k b, (a * j g).mat k (e (some b)) = ∑ c, A k (e (some c)) * g.mat c b := by
    intro k b
    show (A * (j g).mat) k (e (some b)) = _
    rw [Matrix.mul_apply, sum_eq_apply_none_add_sum_some_of_option_equiv e]
    simp [h0b, hcb]
  set u : Fin P' ⊕ Fin Q' → ℂ := fun c => A (e none) (e (some c)) with hu
  have hrowsum : ∀ b, ∑ c, A (e none) (e (some c)) * g.mat c b = u b + ∑ c, u c * D c b := by
    intro b
    rw [hgD]
    simp [Matrix.add_apply, mul_add, Finset.sum_add_distrib, Matrix.one_apply, hu]
  have hblock : ∀ i b, ∑ c, A (e (some i)) (e (some c)) * g.mat c b -
      (1 : Matrix (Fin P' ⊕ Fin Q') (Fin P' ⊕ Fin Q') ℂ) i b = (D + E + E * D) i b := by
    intro i b
    simp_rw [hAE]
    rw [← Matrix.mul_apply, ← Matrix.sub_apply, hgD,
      show (1 + E) * (1 + D) - 1 = D + E + E * D by noncomm_ring]
  have hgauge : _root_.GlobalTheory.CompactDualQuot.gauge (a * j g) = N + ∑ b, ‖u b + ∑ c, u c * D c b‖ +
      ∑ i, (‖y (e (some i))‖ + ∑ b, ‖(D + E + E * D) i b‖) := by
    simp only [_root_.GlobalTheory.CompactDualQuot.gauge, _root_.GlobalTheory.CompactDualQuot.l1, Matrix.sub_apply]
    simp only [sum_eq_apply_none_add_sum_some_of_option_equiv e]
    simp only [hM0, hMb, hrowsum, ← hblock]
    have h1 : ∀ i b, (1 : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) (e (some i)) (e (some b)) =
        (1 : Matrix (Fin P' ⊕ Fin Q') (Fin P' ⊕ Fin Q') ℂ) i b := by
      intro i b; simp [Matrix.one_apply]
    have h2 : ∀ b, (1 : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) (e none) (e (some b)) = 0 := by
      intro b; simp [Matrix.one_apply]
    have h3 : ∀ b, (1 : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) (e (some b)) (e none) = 0 := by
      intro b; simp [Matrix.one_apply]
    simp only [h1, h2, h3, Matrix.one_apply_eq, sub_zero, hN]
  have hL := sum_norm_sum_mul_matrix_le_mul_sum_norm_of_norm_le u D S fun c => (hrow c).le.trans (hyS c)
  have huS : ∑ b, ‖u b‖ = S := Finset.sum_congr rfl fun b _ => hrow b
  have hR_up : ∑ b, ‖u b + ∑ c, u c * D c b‖ ≤ S + S * G := by
    calc ∑ b, ‖u b + ∑ c, u c * D c b‖ ≤ ∑ b, (‖u b‖ + ‖∑ c, u c * D c b‖) :=
          Finset.sum_le_sum fun b _ => norm_add_le _ _
      _ ≤ S + S * G := by rw [Finset.sum_add_distrib, huS]; linarith
  have hR_lo : S - S * G ≤ ∑ b, ‖u b + ∑ c, u c * D c b‖ := by
    calc S - S * G ≤ ∑ b, (‖u b‖ - ‖∑ c, u c * D c b‖) := by
          rw [Finset.sum_sub_distrib, huS]; linarith
      _ ≤ ∑ b, ‖u b + ∑ c, u c * D c b‖ := Finset.sum_le_sum fun b _ => by
          have := norm_sub_le (u b + ∑ c, u c * D c b) (∑ c, u c * D c b)
          rw [add_sub_cancel_right] at this
          linarith
  have hE1 : ∑ i, ∑ b, ‖E i b‖ ≤ S * S := by
    calc ∑ i, ∑ b, ‖E i b‖ ≤ ∑ i, ∑ b, ‖y (e (some i))‖ * ‖y (e (some b))‖ :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun b _ => hEn i b
      _ = S * S := by rw [hS, Finset.sum_mul_sum]
  have hED : ∑ i, ∑ b, ‖(E * D) i b‖ ≤ S * S * G := by
    calc ∑ i, ∑ b, ‖(E * D) i b‖ ≤ ∑ i, ‖y (e (some i))‖ * S * G := by
          refine Finset.sum_le_sum fun i _ => ?_
          simp only [Matrix.mul_apply]
          exact sum_norm_sum_mul_matrix_le_mul_sum_norm_of_norm_le (fun c => E i c) D _ fun c =>
            (hEn i c).trans (mul_le_mul_of_nonneg_left (hyS c) (norm_nonneg _))
      _ = S * S * G := by rw [← Finset.sum_mul, ← Finset.sum_mul]
  have hB_up : ∑ i, ∑ b, ‖(D + E + E * D) i b‖ ≤ G + S * S + S * S * G := by
    calc ∑ i, ∑ b, ‖(D + E + E * D) i b‖ ≤
          ∑ i, ∑ b, (‖D i b‖ + ‖E i b‖ + ‖(E * D) i b‖) :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun b _ => by
            rw [Matrix.add_apply, Matrix.add_apply]
            linarith [norm_add_le (D i b + E i b) ((E * D) i b), norm_add_le (D i b) (E i b)]
      _ = G + ∑ i, ∑ b, ‖E i b‖ + ∑ i, ∑ b, ‖(E * D) i b‖ := by
          simp only [Finset.sum_add_distrib, hG]
      _ ≤ G + S * S + S * S * G := by linarith
  have hB_lo : G - S * S - S * S * G ≤ ∑ i, ∑ b, ‖(D + E + E * D) i b‖ := by
    calc G - S * S - S * S * G ≤ G - ∑ i, ∑ b, ‖E i b‖ - ∑ i, ∑ b, ‖(E * D) i b‖ := by linarith
      _ = ∑ i, ∑ b, (‖D i b‖ - ‖E i b‖ - ‖(E * D) i b‖) := by
          simp only [Finset.sum_sub_distrib, hG]
      _ ≤ ∑ i, ∑ b, ‖(D + E + E * D) i b‖ :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun b _ => by
            rw [Matrix.add_apply, Matrix.add_apply]
            have h := norm_sub_le (D i b + E i b + (E * D) i b - E i b) ((E * D) i b)
            have h' := norm_sub_le (D i b + E i b + (E * D) i b) (E i b)
            rw [show D i b + E i b + (E * D) i b - E i b - (E * D) i b = D i b by ring] at h
            linarith
  rw [hpt, hgg, hgauge, Finset.sum_add_distrib]
  have k1 := mul_le_mul_of_nonneg_right hts hG0
  have k2 := mul_le_mul_of_nonneg_right hts hS0
  have k3 := mul_nonneg ht0.le (mul_nonneg (mul_nonneg hS0 hG0) (by linarith : (0 : ℝ) ≤ 1 - S))
  have k4 := mul_nonneg (by linarith : (0 : ℝ) ≤ t - 1) hN0
  have k5 := mul_nonneg (by linarith : (0 : ℝ) ≤ t - 1) hS0
  have k6 := mul_nonneg (by linarith : (0 : ℝ) ≤ t - 1) (mul_nonneg hS0 hG0)
  have k7 := mul_nonneg (mul_nonneg hS0 hG0) (by linarith : (0 : ℝ) ≤ 1 - S)
  have k8 := mul_nonneg (by linarith : (0 : ℝ) ≤ t - 1) (mul_nonneg hS0 hS0)
  constructor
  · have key : N + 2 * S + G ≤ t * (N + 2 * S + G - S * G - S * S - S * S * G) := by
      nlinarith
    calc N + 2 * S + G ≤ t * (N + 2 * S + G - S * G - S * S - S * S * G) := key
      _ ≤ _ := by
          apply mul_le_mul_of_nonneg_left _ ht0.le
          rw [← hS]
          linarith
  · rw [← hS]
    nlinarith

end GlobalTheory.SectionGaugeCompare
