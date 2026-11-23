import Mathlib
import Formalism.PeriodIntegrals.RhsWLim
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.VolumeLieE
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.MBaseMem
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.RhsTest
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.OrbitPushCut

set_option linter.unusedVariables false

noncomputable section

open MeasureTheory Filter Topology Matrix
open scoped ENNReal

namespace PI.RhsWLim.W

open PI.RhsWLim PI.RhsWLim.W.MB

variable {k r : ℕ}

lemma op_not_mid_cases (i : Fin (2 * r + k + 1)) (hi : ¬ mid k r i) : ∃ a : Fin r, i = eI k r a ∨ i = esI k r a := by
  have := i.isLt
  by_cases h : i.val < r
  · exact ⟨⟨i.val, h⟩, Or.inl rfl⟩
  · refine ⟨⟨2 * r + k - i.val, by omega⟩, Or.inr ?_⟩
    apply Fin.ext
    simp only [esI]
    omega

lemma op_hpk_e (a : Fin r) : Hpk k r *ᵥ bvec (eI k r a) = bvec (esI k r a) := by
  ext l
  rw [mulVec_bvec, bvec_apply]
  have := a.isLt
  have := l.isLt
  unfold Hpk
  simp only [eI, esI, Fin.ext_iff]
  split_ifs <;> first | rfl | (exfalso; omega)

lemma op_hpk_es (a : Fin r) : Hpk k r *ᵥ bvec (esI k r a) = bvec (eI k r a) := by
  ext l
  rw [mulVec_bvec, bvec_apply]
  have := a.isLt
  have := l.isLt
  unfold Hpk
  simp only [eI, esI, Fin.ext_iff]
  split_ifs <;> first | rfl | (exfalso; omega)

lemma op_fix_dual {g : Mat k r} (hg : g ∈ UH (Hpk k r)) {f : Fin (2 * r + k + 1) → ℂ} (hf : g *ᵥ f = f) :
    gᴴ *ᵥ (Hpk k r *ᵥ f) = Hpk k r *ᵥ f := by
  have hg' : gᴴ * Hpk k r * g = Hpk k r := hg
  calc gᴴ *ᵥ (Hpk k r *ᵥ f) = gᴴ *ᵥ (Hpk k r *ᵥ (g *ᵥ f)) := by rw [hf]
    _ = (gᴴ * Hpk k r * g) *ᵥ f := by simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
    _ = Hpk k r *ᵥ f := by rw [hg']

lemma op_uwb_col {g : Mat k r} (hg : g ∈ UWb k r) (i l : Fin (2 * r + k + 1)) (hi : ¬ mid k r i) :
    g l i = if l = i then 1 else 0 := by
  obtain ⟨a, rfl | rfl⟩ := op_not_mid_cases i hi
  · rw [← mulVec_bvec g (eI k r a) l, (hg.2 a).1, bvec_apply]
  · rw [← mulVec_bvec g (esI k r a) l, (hg.2 a).2, bvec_apply]

lemma op_uwb_row {g : Mat k r} (hg : g ∈ UWb k r) (i l : Fin (2 * r + k + 1)) (hi : ¬ mid k r i) :
    g i l = if i = l then 1 else 0 := by
  have key : ∀ j : Fin (2 * r + k + 1), gᴴ *ᵥ bvec j = bvec j → g j l = if j = l then 1 else 0 := by
    intro j hj
    have h := congrFun hj l
    rw [mulVec_bvec, bvec_apply, Matrix.conjTranspose_apply] at h
    have h2 := congrArg star h
    rw [star_star] at h2
    rw [h2]
    by_cases e : l = j
    · rw [if_pos e, if_pos e.symm, star_one]
    · rw [if_neg e, if_neg (fun e' => e e'.symm), star_zero]
  obtain ⟨a, rfl | rfl⟩ := op_not_mid_cases i hi
  · apply key
    have := op_fix_dual hg.1 (hg.2 a).2
    rwa [op_hpk_es] at this
  · apply key
    have := op_fix_dual hg.1 (hg.2 a).1
    rwa [op_hpk_e] at this

lemma op_uwb_eq_emb {g : Mat k r} (hg : g ∈ UWb k r) : g = embWb k r (g.submatrix (wI k r) (wI k r)) := by
  ext i j
  by_cases hj : mid k r j
  · by_cases hi : mid k r i
    · rw [emb_mid _ i j hi hj, Matrix.submatrix_apply, wI_midx, wI_midx]
    · rw [emb_out_row _ i j hi, op_uwb_row hg i j hi]
  · rw [emb_out_col _ i j hj, op_uwb_col hg j i hj]

def toW (k : ℕ) (p : (Fin k → ℂ) × ℂ) : Fin (k + 1) → ℂ := fun j =>
  if h : j.val < k then p.1 ⟨j.val, h⟩ else p.2

def ofW (k : ℕ) (v : Fin (k + 1) → ℂ) : (Fin k → ℂ) × ℂ := (fun i => v (Fin.castSucc i), v (Fin.last k))

def blkAct (k : ℕ) (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (p : (Fin k → ℂ) × ℂ) : (Fin k → ℂ) × ℂ :=
  ofW k (μ *ᵥ toW k p)

def qf (k : ℕ) (p : (Fin k → ℂ) × ℂ) : ℝ := ∑ i, Complex.normSq (p.1 i) - Complex.normSq p.2

def LebInvB : Prop :=
  ∀ (k : ℕ) (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ), μᴴ * Hb k * μ = Hb k →
    (volume : Measure ((Fin k → ℂ) × ℂ)).map (blkAct k μ) = volume

def coneSh (k : ℕ) (T' : ℝ) (E : Set ((Fin k → ℂ) × ℂ)) : Set ((Fin k → ℂ) × ℂ) :=
  (fun q : ((Fin k → ℂ) × ℂ) × ℝ => q.2 • q.1) '' ((E ∩ hypS k T') ×ˢ Set.Ioo (1 : ℝ) 2)

def ConeForm : Prop :=
  ∀ (k : ℕ) (T' : ℝ), 0 < T' → ∃ κ : ℝ≥0∞, κ ≠ 0 ∧ κ ≠ ⊤ ∧
    ∀ E, MeasurableSet E → hypM k T' E = κ * volume (coneSh k T' E)

lemma toW_ofW (v : Fin (k + 1) → ℂ) : toW k (ofW k v) = v := by
  funext j
  unfold toW ofW
  by_cases h : j.val < k
  · rw [dif_pos h]
    congr 1
  · rw [dif_neg h]
    have : j = Fin.last k := Fin.ext (by have := j.isLt; simp only [Fin.val_last]; omega)
    rw [this]

lemma ofW_toW (p : (Fin k → ℂ) × ℂ) : ofW k (toW k p) = p := by
  unfold toW ofW
  ext i
  · simp only [Fin.val_castSucc, i.isLt, dif_pos]
  · simp only [Fin.val_last, lt_irrefl, dif_neg, not_false_eq_true]

lemma blkAct_mul (μ ν : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (p : (Fin k → ℂ) × ℂ) :
    blkAct k μ (blkAct k ν p) = blkAct k (μ * ν) p := by
  unfold blkAct
  rw [toW_ofW, Matrix.mulVec_mulVec]

lemma blkAct_one (p : (Fin k → ℂ) × ℂ) : blkAct k 1 p = p := by
  unfold blkAct
  rw [Matrix.one_mulVec, ofW_toW]

lemma toW_smul (t : ℝ) (p : (Fin k → ℂ) × ℂ) : toW k (t • p) = t • toW k p := by
  funext j
  unfold toW
  by_cases h : j.val < k
  · simp only [dif_pos h, Prod.smul_fst, Pi.smul_apply]
  · simp only [dif_neg h, Prod.smul_snd, Pi.smul_apply]

lemma blkAct_smul (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (t : ℝ) (p : (Fin k → ℂ) × ℂ) :
    blkAct k μ (t • p) = t • blkAct k μ p := by
  unfold blkAct
  rw [toW_smul, Matrix.mulVec_smul]
  rfl

lemma continuous_toW : Continuous (toW k) := by
  refine continuous_pi fun j => ?_
  by_cases h : j.val < k
  · have : (fun p : (Fin k → ℂ) × ℂ => toW k p j) = fun p => p.1 ⟨j.val, h⟩ := by
      funext p; unfold toW; rw [dif_pos h]
    rw [this]
    exact (continuous_apply _).comp continuous_fst
  · have : (fun p : (Fin k → ℂ) × ℂ => toW k p j) = fun p => p.2 := by
      funext p; unfold toW; rw [dif_neg h]
    rw [this]
    exact continuous_snd

lemma continuous_blkAct (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) : Continuous (blkAct k μ) := by
  have hc : Continuous fun p => μ *ᵥ toW k p := Continuous.matrix_mulVec continuous_const continuous_toW
  exact (continuous_pi fun i => (continuous_apply (Fin.castSucc i)).comp hc).prodMk
    ((continuous_apply (Fin.last k)).comp hc)

lemma hb_sq : Hb k * Hb k = 1 := by
  unfold Hb
  rw [Matrix.diagonal_mul_diagonal]
  rw [← Matrix.diagonal_one]
  congr 1
  funext j
  split_ifs <;> norm_num

lemma hb_inv_mul {μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ} (hμ : μᴴ * Hb k * μ = Hb k) :
    (Hb k * μᴴ * Hb k) * μ = 1 := by
  calc (Hb k * μᴴ * Hb k) * μ = Hb k * (μᴴ * Hb k * μ) := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hμ, hb_sq]

lemma qf_eq (p : (Fin k → ℂ) × ℂ) : (qf k p : ℂ) = star (toW k p) ⬝ᵥ (Hb k *ᵥ toW k p) := by
  unfold qf
  rw [dotProduct]
  simp only [Hb, Matrix.mulVec_diagonal, Pi.star_apply]
  rw [Fin.sum_univ_castSucc]
  have h1 : ∀ i : Fin k, toW k p (Fin.castSucc i) = p.1 i := fun i => by
    unfold toW; rw [dif_pos (by simp)]; rfl
  have h2 : toW k p (Fin.last k) = p.2 := by
    unfold toW; rw [dif_neg (by simp)]
  have hz : ∀ z : ℂ, star z * z = (Complex.normSq z : ℂ) := fun z => by
    rw [Complex.normSq_eq_conj_mul_self]; rfl
  simp only [h1, h2, Fin.castSucc_ne_last, if_false, if_true, one_mul, neg_one_mul, mul_neg, hz]
  push_cast
  ring

lemma qf_blkAct {μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ} (hμ : μᴴ * Hb k * μ = Hb k) (p : (Fin k → ℂ) × ℂ) :
    qf k (blkAct k μ p) = qf k p := by
  have h : (qf k (blkAct k μ p) : ℂ) = (qf k p : ℂ) := by
    rw [qf_eq, qf_eq]
    unfold blkAct
    rw [toW_ofW, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hμ]
  exact_mod_cast h

lemma hypS_iff (T' : ℝ) (p : (Fin k → ℂ) × ℂ) : p ∈ hypS k T' ↔ qf k p = -T' := Iff.rfl

lemma opAct_emb (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (p : (Fin k → ℂ) × ℂ) :
    opAct k r (embWb k r μ) p = blkAct k μ p := by
  have key : ∀ j : Fin (k + 1), (embWb k r μ *ᵥ opVec k r p) (wI k r j) = (μ *ᵥ toW k p) j := by
    intro j
    have hv : ∀ m : Fin (k + 1), opVec k r p (wI k r m) = toW k p m := by
      intro m
      have := m.isLt
      unfold opVec toW wI
      by_cases h : m.val < k
      · rw [dif_pos (by simp only; omega), dif_pos h]
        exact congrArg p.1 (Fin.ext (by simp))
      · rw [dif_neg (by simp only; omega), dif_neg h, if_pos (by simp only; omega)]
    show ∑ i, embWb k r μ (wI k r j) i * opVec k r p i = ∑ m, μ j m * toW k p m
    rw [sum_wb]
    · exact Finset.sum_congr rfl fun m _ => by rw [embWb_wI, hv]
    · intro i hi
      have : opVec k r p i = 0 := by
        unfold opVec
        rw [dif_neg (by omega), if_neg (by omega)]
      rw [this, mul_zero]
  unfold opAct opCo blkAct ofW
  ext i
  · exact key _
  · exact key _

lemma opAct_uwb {s : Mat k r} (hs : s ∈ UWb k r) :
    ∃ μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ, μᴴ * Hb k * μ = Hb k ∧ opAct k r s = blkAct k μ := by
  refine ⟨s.submatrix (wI k r) (wI k r), ?_, ?_⟩
  · rw [← emb_mem (r := r), ← op_uwb_eq_emb hs]
    exact hs.1
  · funext p
    conv_lhs => rw [op_uwb_eq_emb hs]
    exact opAct_emb _ p

theorem hypInv_of (hL : LebInvB) (hC : ConeForm) : HypInv := by
  intro k r T' hk hT' s hs
  obtain ⟨μ, hμ, hse⟩ := opAct_uwb hs
  rw [hse]
  set ν := Hb k * μᴴ * Hb k with hν
  have hνμ : ν * μ = 1 := hb_inv_mul hμ
  have hμν : μ * ν = 1 := mul_eq_one_comm.1 hνμ
  let e : ((Fin k → ℂ) × ℂ) ≃ᵐ ((Fin k → ℂ) × ℂ) :=
    { toFun := blkAct k μ
      invFun := blkAct k ν
      left_inv := fun p => by simp only [blkAct_mul, hνμ, blkAct_one]
      right_inv := fun p => by simp only [blkAct_mul, hμν, blkAct_one]
      measurable_toFun := (continuous_blkAct μ).measurable
      measurable_invFun := (continuous_blkAct ν).measurable }
  obtain ⟨κ, -, -, hκ⟩ := hC k T' hT'
  have hset : ∀ E, coneSh k T' (blkAct k μ ⁻¹' E) = blkAct k μ ⁻¹' coneSh k T' E := by
    intro E
    ext x
    constructor
    · rintro ⟨⟨v, t⟩, ⟨⟨hvE, hvS⟩, ht⟩, rfl⟩
      refine ⟨(blkAct k μ v, t), ⟨⟨hvE, ?_⟩, ht⟩, ?_⟩
      · rw [hypS_iff, qf_blkAct hμ]; exact hvS
      · exact (blkAct_smul μ t v).symm
    · rintro ⟨⟨w, t⟩, ⟨⟨hwE, hwS⟩, ht⟩, hx⟩
      have hw : blkAct k μ (blkAct k ν w) = w := by rw [blkAct_mul, hμν, blkAct_one]
      refine ⟨(blkAct k ν w, t), ⟨⟨?_, ?_⟩, ht⟩, ?_⟩
      · show blkAct k μ (blkAct k ν w) ∈ E
        rw [hw]; exact hwE
      · rw [hypS_iff, ← qf_blkAct hμ, hw]; exact hwS
      · have h1 : blkAct k μ (t • blkAct k ν w) = blkAct k μ x := by
          rw [blkAct_smul, hw]; exact hx
        have h2 := congrArg (blkAct k ν) h1
        simp only [blkAct_mul, hνμ, blkAct_one] at h2
        exact h2
  ext E hE
  rw [Measure.map_apply (continuous_blkAct μ).measurable hE,
    hκ _ ((continuous_blkAct μ).measurable hE), hκ _ hE, hset]
  congr 1
  have := MeasurableEquiv.map_apply e (μ := (volume : Measure ((Fin k → ℂ) × ℂ))) (coneSh k T' E)
  have hmap : (volume : Measure ((Fin k → ℂ) × ℂ)).map e = volume := hL k μ hμ
  rw [hmap] at this
  exact this.symm

end PI.RhsWLim.W
