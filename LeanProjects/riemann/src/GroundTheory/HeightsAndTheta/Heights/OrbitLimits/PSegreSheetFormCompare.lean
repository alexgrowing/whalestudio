import Mathlib
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StSegreSheetFormCompare
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSheetFormCompare
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix Filter Topology ReciprocityTheory.AnForm
open ReciprocityTheory.AnForm.A (jacC)
open ReciprocityTheory.ChartRestriction.G.Geo (HermLine IsSmoothHerm pot segre)
open scoped ContDiff ComplexOrder

noncomputable section

namespace SegreSheetFormComparison

theorem hessC_finset_sum {D : ℕ} {α : Type*} (s : Finset α) (f : α → (Fin D → ℂ) → ℝ) (z : Fin D → ℂ)
    (hf : ∀ a ∈ s, ContDiffAt ℝ 2 (f a) z) :
    hessC (fun w => ∑ a ∈ s, f a w) z = ∑ a ∈ s, hessC (f a) z := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    ext i j
    simp [hessC]
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    rw [ReciprocityTheory.AnForm.A.hessC_add (f a) (fun w => ∑ b ∈ s, f b w) z (hf a (Finset.mem_insert_self a s))
      (ContDiffAt.sum fun b hb => hf b (Finset.mem_insert_of_mem hb)),
      ih fun b hb => hf b (Finset.mem_insert_of_mem hb)]

theorem hessC_add_sum_log {D : ℕ} {α : Type*} (s : Finset α) (φ : (Fin D → ℂ) → ℝ) (c : α → ℝ)
    (g : α → (Fin D → ℂ) → ℂ) (z : Fin D → ℂ) (hφ : ContDiffAt ℝ 2 φ z) (hg : ∀ a, AnalyticAt ℂ (g a) z)
    (hz : ∀ a, g a z ≠ 0) :
    hessC (fun w => φ w + ∑ a ∈ s, c a * Real.log ‖g a w‖) z = hessC φ z := by
  have hc : ∀ a, ContDiffAt ℝ 2 (fun w => c a * Real.log ‖g a w‖) z := fun a =>
    contDiffAt_const.mul ((((hg a).contDiffAt (n := 2)).restrict_scalars ℝ).norm ℝ (hz a) |>.log
      (norm_ne_zero_iff.2 (hz a)))
  rw [ReciprocityTheory.AnForm.A.hessC_add _ _ z hφ (ContDiffAt.sum fun a _ => hc a),
    hessC_finset_sum s _ z fun a _ => hc a]
  simp [ReciprocityTheory.AnForm.M.hessC_const_mul', ReciprocityTheory.AnForm.A.hessC_log_norm _ z (hg _) (hz _)]

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]

omit [DecidableEq K] in

theorem sum_norm_segre_sq [DecidableEq K] (w : (Σ k, ι k) → ℂ) :
    ∑ i', ‖segre w i'‖ ^ 2 = ∏ k, ∑ j, ‖w ⟨k, j⟩‖ ^ 2 := by
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  simp [segre, norm_prod, Finset.prod_pow]

omit [DecidableEq K] [∀ k, Fintype (ι k)] in

theorem log_h_smul (A : HermLine ι) (c : K → ℂ) (w : (Σ k, ι k) → ℂ) (hc : ∀ k, c k ≠ 0)
    (hw : ∀ k, ∃ j, w ⟨k, j⟩ ≠ 0) :
    Real.log (A.h (fun p => c p.1 * w p)) = Real.log (A.h w) + ∑ k, (A.a k : ℝ) * Real.log ‖c k‖ := by
  have hp : ∀ k, 0 < ‖c k‖ ^ A.a k := fun k => zpow_pos (norm_pos_iff.2 (hc k)) _
  rw [A.smul c w hc, Real.log_mul (Finset.prod_pos fun k _ => hp k).ne' (A.pos w hw).ne',
    Real.log_prod (fun k _ => (hp k).ne'), add_comm]
  simp [Real.log_zpow]

variable (ι) in

def nk (k : K) : ℕ := Fintype.card (ι k) - 1

open Classical in

def eK (jj : (k : K) → ι k) (k : K) : {j : ι k // j ≠ jj k} ≃ Fin (nk ι k) :=
  Fintype.equivFinOfCardEq (by simp [nk, Fintype.card_subtype_compl])

variable (ι) in

def NN : ℕ := Fintype.card (Σ k, Fin (nk ι k))

variable (ι) in

def eS : (Σ k, Fin (nk ι k)) ≃ Fin (NN ι) := Fintype.equivFin _

variable (ι) in

def blk (k : K) : (Fin (NN ι) → ℂ) →L[ℂ] (Fin (nk ι k) → ℂ) :=
  ContinuousLinearMap.pi fun r => ContinuousLinearMap.proj (eS ι ⟨k, r⟩)

open Classical in

def ins (jj : (k : K) → ι k) (t : Fin (NN ι) → ℂ) : (Σ k, ι k) → ℂ :=
  fun p => if h : p.2 = jj p.1 then 1 else t (eS ι ⟨p.1, eK jj p.1 ⟨p.2, h⟩⟩)

def pt (jj : (k : K) → ι k) (a : Fin (NN ι)) : Σ k, ι k :=
  ⟨((eS ι).symm a).1, ((eK jj _).symm ((eS ι).symm a).2).1⟩

def nrm (jj : (k : K) → ι k) (w : (Σ k, ι k) → ℂ) : Fin (NN ι) → ℂ :=
  fun a => w (pt jj a) / w ⟨(pt jj a).1, jj (pt jj a).1⟩

variable (ι) in

def FSG (t : Fin (NN ι) → ℂ) : ℝ := ∑ k, (1 / 2) * HilbertSamuel.ProjFS.logPot (blk ι k t)

section Chart

variable (jj : (k : K) → ι k)

omit [DecidableEq K] in
theorem ins_anchor (t : Fin (NN ι) → ℂ) (k : K) : ins jj t ⟨k, jj k⟩ = 1 := by
  simp [ins]

omit [DecidableEq K] in
theorem ins_ne (t : Fin (NN ι) → ℂ) {k : K} {j : ι k} (h : j ≠ jj k) :
    ins jj t ⟨k, j⟩ = t (eS ι ⟨k, eK jj k ⟨j, h⟩⟩) := by
  simp [ins, h]

omit [DecidableEq K] in

theorem ins_blockNonzero (t : Fin (NN ι) → ℂ) : ∀ k, ∃ j, ins jj t ⟨k, j⟩ ≠ 0 :=
  fun k => ⟨jj k, by rw [ins_anchor]; exact one_ne_zero⟩

omit [DecidableEq K] in
theorem contDiff_ins : ContDiff ℝ ∞ (ins jj) := by
  refine contDiff_pi.2 fun p => ?_
  obtain ⟨k, j⟩ := p
  by_cases h : j = jj k
  · subst h
    simp only [ins_anchor]
    exact contDiff_const
  · simp only [ins_ne jj _ h]
    exact contDiff_apply ℝ ℂ _

omit [DecidableEq K] in
theorem pt_eS {k : K} {j : ι k} (h : j ≠ jj k) : pt jj (eS ι ⟨k, eK jj k ⟨j, h⟩⟩) = ⟨k, j⟩ := by
  unfold pt
  rw [Equiv.symm_apply_apply]
  simp

omit [DecidableEq K] in

theorem eq_smul_ins (w : (Σ k, ι k) → ℂ) (hw : ∀ k, w ⟨k, jj k⟩ ≠ 0) :
    w = fun p => w ⟨p.1, jj p.1⟩ * ins jj (nrm jj w) p := by
  funext ⟨k, j⟩
  by_cases h : j = jj k
  · subst h
    simp [ins_anchor]
  · rw [ins_ne jj _ h]
    simp only [nrm]
    rw [pt_eS jj h]
    dsimp only
    rw [mul_div_cancel₀ _ (hw k)]

omit [DecidableEq K] in

theorem sum_ins_sq (t : Fin (NN ι) → ℂ) (k : K) :
    ∑ j, ‖ins jj t ⟨k, j⟩‖ ^ 2 = 1 + ∑ r, ‖blk ι k t r‖ ^ 2 := by
  classical
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (jj k)), ins_anchor, norm_one, one_pow]
  congr 1
  rw [Finset.sum_subtype (p := fun j => j ≠ jj k) _ (fun j => by simp)]
  rw [← Equiv.sum_comp (eK jj k).symm]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [ins_ne jj _ ((eK jj k).symm r).2]
  simp [blk]

omit [DecidableEq K] in

theorem norm_nrm_le (w : (Σ k, ι k) → ℂ) (hmax : ∀ k j, ‖w ⟨k, j⟩‖ ≤ ‖w ⟨k, jj k⟩‖) :
    ‖nrm jj w‖ ≤ 1 := by
  refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun a => ?_
  simp only [nrm, norm_div]
  exact div_le_one_of_le₀ (hmax _ _) (norm_nonneg _)

theorem log_segre_eq (w : (Σ k, ι k) → ℂ) (hw : ∀ k, w ⟨k, jj k⟩ ≠ 0) :
    Real.log (Real.sqrt (∑ i', ‖segre w i'‖ ^ 2)) =
      FSG ι (nrm jj w) + ∑ k, (1 : ℝ) * Real.log ‖w ⟨k, jj k⟩‖ := by
  have he := eq_smul_ins jj w hw
  have hk : ∀ k, ∑ j, ‖w ⟨k, j⟩‖ ^ 2 =
      ‖w ⟨k, jj k⟩‖ ^ 2 * (1 + ∑ r, ‖blk ι k (nrm jj w) r‖ ^ 2) := by
    intro k
    rw [← sum_ins_sq, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    have := congrFun he ⟨k, j⟩
    dsimp only at this
    rw [this, norm_mul, mul_pow]
  have hpos : ∀ k, 0 < ‖w ⟨k, jj k⟩‖ ^ 2 * (1 + ∑ r, ‖blk ι k (nrm jj w) r‖ ^ 2) := fun k =>
    mul_pos (pow_pos (norm_pos_iff.2 (hw k)) 2) (by positivity)
  have hlp : ∀ k, HilbertSamuel.ProjFS.logPot (blk ι k (nrm jj w)) =
      Real.log (1 + ∑ r, ‖blk ι k (nrm jj w) r‖ ^ 2) := fun k => rfl
  rw [sum_norm_segre_sq, Finset.prod_congr rfl fun k _ => hk k,
    Real.log_sqrt (Finset.prod_nonneg fun k _ => (hpos k).le),
    Real.log_prod (fun k _ => (hpos k).ne'), FSG, Finset.sum_div, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Real.log_mul (pow_pos (norm_pos_iff.2 (hw k)) 2).ne' (by positivity), Real.log_pow, hlp]
  push_cast
  ring

omit [DecidableEq K] in

theorem pot_eq {e : ℕ} (L : Fin e → HermLine ι) (j : Fin e) (w : (Σ k, ι k) → ℂ)
    (hw : ∀ k, w ⟨k, jj k⟩ ≠ 0) :
    pot L j w = pot L j (ins jj (nrm jj w)) + ∑ k, ((L j).a k : ℝ) * Real.log ‖w ⟨k, jj k⟩‖ := by
  have he := eq_smul_ins jj w hw
  show Real.log ((L j).h w) = Real.log ((L j).h _) + _
  conv_lhs => rw [he]
  exact log_h_smul (L j) (fun k => w ⟨k, jj k⟩) _ hw (ins_blockNonzero jj _)

end Chart

section Analysis

variable (jj : (k : K) → ι k)

omit [DecidableEq K] in
theorem contDiff_FSG : ContDiff ℝ 2 (FSG ι) := by
  unfold FSG
  exact ContDiff.sum fun k _ => contDiff_const.mul
    (((SheetFormComparison.contDiff_logPot _).of_le (WithTop.coe_le_coe.2 le_top)).comp
      ((blk ι k).contDiff.restrict_scalars ℝ))

omit [DecidableEq K] in

theorem contDiff_pot_ins {e : ℕ} (L : Fin e → HermLine ι) (j : Fin e) (hL : IsSmoothHerm (L j)) :
    ContDiff ℝ 2 (fun t => pot L j (ins jj t)) := by
  refine contDiff_iff_contDiffAt.2 fun t => ?_
  have hh : ContDiffAt ℝ 2 (L j).h (ins jj t) :=
    (hL.contDiffAt (ReciprocityTheory.ChartRestriction.G.Geo.isOpen_blockNonzero.mem_nhds (ins_blockNonzero jj t))).of_le
      (WithTop.coe_le_coe.2 le_top)
  exact (hh.comp t ((contDiff_ins jj).of_le (WithTop.coe_le_coe.2 le_top)).contDiffAt).log
    ((L j).pos _ (ins_blockNonzero jj t)).ne'

omit [DecidableEq K] in

theorem sum_jacC_blk (t : Fin (NN ι) → ℂ) :
    ∑ k, (jacC (⇑(blk ι k)) t)ᵀ * (jacC (⇑(blk ι k)) t).map (starRingEnd ℂ) = 1 := by
  classical
  have hj : ∀ k, jacC (⇑(blk ι k)) t =
      Matrix.of fun r b => (Pi.single b (1 : ℂ) : Fin (NN ι) → ℂ) (eS ι ⟨k, r⟩) := by
    intro k
    ext r b
    simp only [jacC, Matrix.of_apply, ContinuousLinearMap.fderiv]
    rfl
  ext b c
  simp only [hj, Matrix.sum_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
    Matrix.of_apply]
  rw [← Fintype.sum_sigma (fun q : Σ k, Fin (nk ι k) => (Pi.single b (1 : ℂ) : Fin (NN ι) → ℂ) (eS ι q) *
    (starRingEnd ℂ) ((Pi.single c (1 : ℂ) : Fin (NN ι) → ℂ) (eS ι q))),
    Equiv.sum_comp (eS ι) (fun a => (Pi.single b (1 : ℂ) : Fin (NN ι) → ℂ) a *
      (starRingEnd ℂ) ((Pi.single c (1 : ℂ) : Fin (NN ι) → ℂ) a))]
  simp [Pi.single_apply, Matrix.one_apply, eq_comm]

omit [DecidableEq K] in

theorem hessC_FSG_lower (t : Fin (NN ι) → ℂ) (ht : ‖t‖ ≤ 1) :
    ((((2 * (1 + NN ι : ℝ) ^ 2 : ℝ)) : ℂ) • hessC (FSG ι) t - 1).PosSemidef := by
  set m : ℝ := (1 + NN ι : ℝ) ^ 2 with hm
  have hlp : ∀ k, ContDiffAt ℝ 2 (HilbertSamuel.ProjFS.logPot (N := nk ι k)) (blk ι k t) := fun k =>
    ((SheetFormComparison.contDiff_logPot _).of_le (WithTop.coe_le_coe.2 le_top)).contDiffAt
  have hH : hessC (FSG ι) t = ∑ k, ((1 / 2 : ℝ) : ℂ) • ((jacC (⇑(blk ι k)) t)ᵀ *
      hessC HilbertSamuel.ProjFS.logPot (blk ι k t) * (jacC (⇑(blk ι k)) t).map (starRingEnd ℂ)) := by
    rw [show FSG ι = fun t => ∑ k, (1 / 2 : ℝ) * HilbertSamuel.ProjFS.logPot (blk ι k t) from rfl,
      hessC_finset_sum]
    · refine Finset.sum_congr rfl fun k _ => ?_
      rw [ReciprocityTheory.AnForm.M.hessC_const_mul',
        show (fun w => HilbertSamuel.ProjFS.logPot (blk ι k w)) = HilbertSamuel.ProjFS.logPot ∘ ⇑(blk ι k) from rfl,
        ReciprocityTheory.AnForm.A.hessC_comp _ _ t ((blk ι k).analyticAt t) (hlp k)]
    · intro k _
      exact contDiffAt_const.mul ((hlp k).comp t ((blk ι k).contDiff.restrict_scalars ℝ).contDiffAt)
  have hnk : ∀ k, (nk ι k : ℝ) ≤ NN ι := fun k => by
    have : NN ι = ∑ k, nk ι k := by simp [NN, Fintype.card_sigma]
    rw [this]
    exact_mod_cast Finset.single_le_sum (f := fun k => nk ι k) (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)
  have hP1 : ∀ k, (((m : ℝ) : ℂ) • hessC HilbertSamuel.ProjFS.logPot (blk ι k t) - 1).PosSemidef := fun k => by
    have hb : ‖blk ι k t‖ ≤ 1 := (pi_norm_le_iff_of_nonneg zero_le_one).2 fun r => by
      simp only [blk, ContinuousLinearMap.pi_apply, ContinuousLinearMap.proj_apply]
      exact (norm_le_pi_norm t _).trans ht
    have h1 := SheetFormComparison.posSemidef_hessC_logPot_sub hb
    have h0 : (hessC (HilbertSamuel.ProjFS.logPot (N := nk ι k)) (blk ι k t)).PosSemidef :=
      ReciprocityTheory.AnForm.M.hessC_posSemidef _ _ (hlp k)
        (fun w => HilbertSamuel.ProjFS.levi_logPot_nonneg _ w)
    have hd : (0 : ℂ) ≤ ((m - (1 + nk ι k : ℝ) ^ 2 : ℝ) : ℂ) := Complex.zero_le_real.2 (by
      rw [hm, sub_nonneg]
      have := hnk k
      have h0 : (0 : ℝ) ≤ nk ι k := Nat.cast_nonneg _
      nlinarith)
    have e1 : ((m : ℝ) : ℂ) • hessC HilbertSamuel.ProjFS.logPot (blk ι k t) - 1 =
        ((m - (1 + nk ι k : ℝ) ^ 2 : ℝ) : ℂ) • hessC HilbertSamuel.ProjFS.logPot (blk ι k t) +
          ((((1 + nk ι k : ℝ) ^ 2 : ℝ) : ℂ) • hessC HilbertSamuel.ProjFS.logPot (blk ι k t) - 1) := by
      push_cast
      module
    rw [e1]
    exact (h0.smul hd).add h1
  have hBJ : ∀ k, ((jacC (⇑(blk ι k)) t).map (starRingEnd ℂ))ᴴ = (jacC (⇑(blk ι k)) t)ᵀ := fun k => by
    ext a b
    simp
  have key : (((2 * m : ℝ)) : ℂ) • hessC (FSG ι) t - 1 =
      ∑ k, ((jacC (⇑(blk ι k)) t).map (starRingEnd ℂ))ᴴ *
        (((m : ℝ) : ℂ) • hessC HilbertSamuel.ProjFS.logPot (blk ι k t) - 1) *
          (jacC (⇑(blk ι k)) t).map (starRingEnd ℂ) := by
    rw [hH, ← sum_jacC_blk t, Finset.smul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hBJ k, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.mul_smul, Matrix.smul_mul, smul_smul]
    congr 2
    push_cast
    ring
  rw [key]
  exact Matrix.posSemidef_sum _ fun k _ => (hP1 k).conjTranspose_mul_mul_same _

end Analysis

end SegreSheetFormComparison

open SegreSheetFormComparison in

theorem SegreSheetFormCompare.proof : SegreSheetFormCompare.Statement := by
  classical
  intro K _ _ ι _ e L hL
  have hb : ∀ jj : (k : K) → ι k, ∃ a : ℝ, 0 ≤ a ∧ ∀ j, ∀ t ∈ Metric.closedBall (0 : Fin (NN ι) → ℂ) 1,
      (hessC (fun t => pot L j (ins jj t)) t + (a : ℂ) • 1).PosSemidef ∧
        (-hessC (fun t => pot L j (ins jj t)) t + (a : ℂ) • 1).PosSemidef := fun jj =>
    TubeFormComparison.exists_hessC_bound (fun j t => pot L j (ins jj t)) _ (isCompact_closedBall 0 1)
      (fun _ => Set.univ) (fun _ => isOpen_univ) (fun _ => Set.subset_univ _)
      (fun j => (contDiff_pot_ins jj L j (hL j)).contDiffOn)
  choose a ha0 ha using hb
  set A : ℝ := ∑ jj, a jj with hAdef
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun jj _ => ha0 jj
  set C0 : ℝ := 2 * A * (1 + NN ι : ℝ) ^ 2 with hC0
  have hC00 : 0 ≤ C0 := by positivity
  refine ⟨3 ^ e * C0 ^ e, fun z U y hU hyU hzd hzy => ?_⟩

  have hmax : ∀ k, ∃ j, ∀ j', ‖z y ⟨k, j'⟩‖ ≤ ‖z y ⟨k, j⟩‖ := fun k => by
    obtain ⟨j0, -⟩ := hzy k
    have : Nonempty (ι k) := ⟨j0⟩
    obtain ⟨j, -, hj⟩ := Finset.exists_max_image Finset.univ (fun j => ‖z y ⟨k, j⟩‖) Finset.univ_nonempty
    exact ⟨j, fun j' => hj j' (Finset.mem_univ _)⟩
  choose jj hjj using hmax
  have hd0 : ∀ k, z y ⟨k, jj k⟩ ≠ 0 := fun k => by
    obtain ⟨j0, hj0⟩ := hzy k
    intro h0
    apply hj0
    have := hjj k j0
    rw [h0, norm_zero] at this
    exact norm_le_zero_iff.1 this
  have hza : ∀ p, AnalyticAt ℂ (fun y' => z y' p) y := fun p =>
    ReciprocityTheory.AnForm.Osgood.osgood _ U (fun y' => z y' p) hU (differentiableOn_pi.1 hzd p) y hyU

  set τ : (Fin e → ℂ) → Fin (NN ι) → ℂ := fun y' => nrm jj (z y') with hτdef
  have hτa : AnalyticAt ℂ τ y := analyticAt_pi_iff.2 fun b => (hza _).div (hza _) (hd0 _)
  have hτK : τ y ∈ Metric.closedBall (0 : Fin (NN ι) → ℂ) 1 :=
    mem_closedBall_zero_iff.2 (norm_nrm_le jj (z y) hjj)
  have hev : ∀ᶠ y' in 𝓝 y, ∀ k, z y' ⟨k, jj k⟩ ≠ 0 :=
    Filter.eventually_all.2 fun k => (hza _).continuousAt.eventually_ne (hd0 k)
  have hτc : ContDiffAt ℝ 2 τ y := (hτa.contDiffAt (n := 2)).restrict_scalars ℝ
  set Bm := (jacC τ y).map (starRingEnd ℂ) with hBm
  have hBJ : Bmᴴ = (jacC τ y)ᵀ := by
    ext a b
    simp [hBm]

  have hLs : hessC ((fun w => Real.log (Real.sqrt (∑ i', ‖segre w i'‖ ^ 2))) ∘ z) y =
      Bmᴴ * hessC (FSG ι) (τ y) * Bm := by
    have hg : ((fun w => Real.log (Real.sqrt (∑ i', ‖segre w i'‖ ^ 2))) ∘ z) =ᶠ[𝓝 y]
        fun y' => (FSG ι ∘ τ) y' + ∑ k, (1 : ℝ) * Real.log ‖z y' ⟨k, jj k⟩‖ := by
      filter_upwards [hev] with y' hy'
      exact log_segre_eq jj (z y') hy'
    rw [SheetFormComparison.hessC_congr hg, hessC_add_sum_log _ _ _ (fun k y' => z y' ⟨k, jj k⟩) y
      ((contDiff_FSG (ι := ι)).contDiffAt.comp y hτc) (fun k => hza _) hd0, hBJ]
    exact ReciprocityTheory.AnForm.A.hessC_comp (FSG ι) τ y hτa (contDiff_FSG (ι := ι)).contDiffAt
  have hη : ∀ j, hessC (pot L j ∘ z) y = Bmᴴ * hessC (fun t => pot L j (ins jj t)) (τ y) * Bm := fun j => by
    have hg : pot L j ∘ z =ᶠ[𝓝 y] fun y' => ((fun t => pot L j (ins jj t)) ∘ τ) y' +
        ∑ k, ((L j).a k : ℝ) * Real.log ‖z y' ⟨k, jj k⟩‖ := by
      filter_upwards [hev] with y' hy'
      exact pot_eq jj L j (z y') hy'
    rw [SheetFormComparison.hessC_congr hg, hessC_add_sum_log _ _ _ (fun k y' => z y' ⟨k, jj k⟩) y
      ((contDiff_pot_ins jj L j (hL j)).contDiffAt.comp y hτc) (fun k => hza _) hd0, hBJ]
    exact ReciprocityTheory.AnForm.A.hessC_comp _ τ y hτa (contDiff_pot_ins jj L j (hL j)).contDiffAt

  have hlow := hessC_FSG_lower (τ y) (mem_closedBall_zero_iff.1 hτK)
  have haj : a jj ≤ A := Finset.single_le_sum (f := a) (fun j _ => ha0 j) (Finset.mem_univ jj)
  have hAa : (0 : ℂ) ≤ ((A - a jj : ℝ) : ℂ) := Complex.zero_le_real.2 (by linarith)
  have hAc : (0 : ℂ) ≤ (A : ℂ) := Complex.zero_le_real.2 hA0
  have hmid : ∀ j, ((C0 : ℂ) • hessC (FSG ι) (τ y) - hessC (fun t => pot L j (ins jj t)) (τ y)).PosSemidef ∧
      (hessC (fun t => pot L j (ins jj t)) (τ y) + (C0 : ℂ) • hessC (FSG ι) (τ y)).PosSemidef := fun j => by
    obtain ⟨hP1, hP2⟩ := ha jj j (τ y) hτK
    constructor
    · have e1 : (C0 : ℂ) • hessC (FSG ι) (τ y) - hessC (fun t => pot L j (ins jj t)) (τ y) =
          (A : ℂ) • ((((2 * (1 + NN ι : ℝ) ^ 2 : ℝ)) : ℂ) • hessC (FSG ι) (τ y) - 1) +
            (-hessC (fun t => pot L j (ins jj t)) (τ y) + (a jj : ℂ) • 1) + ((A - a jj : ℝ) : ℂ) • 1 := by
        rw [hC0]
        push_cast
        module
      rw [e1]
      exact ((hlow.smul hAc).add hP2).add (Matrix.PosSemidef.one.smul hAa)
    · have e1 : hessC (fun t => pot L j (ins jj t)) (τ y) + (C0 : ℂ) • hessC (FSG ι) (τ y) =
          (A : ℂ) • ((((2 * (1 + NN ι : ℝ) ^ 2 : ℝ)) : ℂ) • hessC (FSG ι) (τ y) - 1) +
            (hessC (fun t => pot L j (ins jj t)) (τ y) + (a jj : ℂ) • 1) + ((A - a jj : ℝ) : ℂ) • 1 := by
        rw [hC0]
        push_cast
        module
      rw [e1]
      exact ((hlow.smul hAc).add hP1).add (Matrix.PosSemidef.one.smul hAa)

  have hmain := ReciprocityTheory.AnForm.A.norm_mdisc_le_of_abs_le
    (fun j => hessC (pot L j ∘ z) y)
    (fun _ => (C0 : ℂ) • hessC ((fun w => Real.log (Real.sqrt (∑ i', ‖segre w i'‖ ^ 2))) ∘ z) y)
    (fun j => by
      rw [hLs, hη j, ← Matrix.smul_mul, ← Matrix.mul_smul, ← Matrix.sub_mul, ← Matrix.mul_sub]
      exact (hmid j).1.conjTranspose_mul_mul_same Bm)
    (fun j => by
      rw [hLs, hη j, ← Matrix.smul_mul, ← Matrix.mul_smul, ← Matrix.add_mul, ← Matrix.mul_add]
      exact (hmid j).2.conjTranspose_mul_mul_same Bm)
  have hs : mdisc (fun _ : Fin e =>
      (C0 : ℂ) • hessC ((fun w => Real.log (Real.sqrt (∑ i', ‖segre w i'‖ ^ 2))) ∘ z) y) =
      (C0 : ℂ) ^ e * mdisc (fun _ : Fin e =>
        hessC ((fun w => Real.log (Real.sqrt (∑ i', ‖segre w i'‖ ^ 2))) ∘ z) y) :=
    IndefiniteRowSideFullHecke.ComplexSets.mdisc_const_smul _ _
  rw [hs, ← Complex.ofReal_pow, Complex.re_ofReal_mul] at hmain
  have hmd : ∀ Φ : Fin e → (Fin e → ℂ) → ℝ, maDens Φ y =
      (e.factorial : ℝ) * (2 / Real.pi) ^ e * (mdisc fun k => hessC (Φ k) y).re := fun Φ => rfl
  rw [hmd, hmd, abs_mul]
  have hK0 : 0 ≤ (e.factorial : ℝ) * (2 / Real.pi) ^ e := by positivity
  rw [abs_of_nonneg hK0]
  calc (e.factorial : ℝ) * (2 / Real.pi) ^ e * |(mdisc fun j => hessC (pot L j ∘ z) y).re|
      ≤ (e.factorial : ℝ) * (2 / Real.pi) ^ e * ‖mdisc fun j => hessC (pot L j ∘ z) y‖ :=
        mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm _) hK0
    _ ≤ (e.factorial : ℝ) * (2 / Real.pi) ^ e * (3 ^ e * (C0 ^ e * (mdisc fun _ : Fin e =>
          hessC ((fun w => Real.log (Real.sqrt (∑ i', ‖segre w i'‖ ^ 2))) ∘ z) y).re)) :=
        mul_le_mul_of_nonneg_left hmain hK0
    _ = _ := by ring

end

end GroundTheory.Heights₂.Heights
