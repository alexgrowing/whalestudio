import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StTubeCollarCompare
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PTubeFormCompare
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Matrix Filter Topology ReciprocityTheory.AnForm ComplexSets
open scoped ContDiff ComplexOrder

noncomputable section

namespace TubeCollarComparison

theorem contDiffAt_logSq_comp {n m : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) (P : MvPolynomial (Fin m) ℂ)
    (x : Fin n → ℂ) (hP : eval (A *ᵥ x) P ≠ 0) :
    ContDiffAt ℝ 2 (fun x => logAbsSq P (A *ᵥ x) ^ 2 / 2) x := by
  have h1 : ContDiffAt ℝ 2 (fun z => ‖eval z P‖ ^ 2) (A *ᵥ x) :=
    (((TubeFormComparison.analyticAt_eval P _).contDiffAt (n := 2)).restrict_scalars ℝ).norm_sq ℝ
  have hv : ContDiffAt ℝ 2 (logAbsSq P) (A *ᵥ x) := h1.log (pow_ne_zero 2 (norm_ne_zero_iff.2 hP))
  have hA : ContDiff ℝ 2 (fun x : Fin n → ℂ => A *ᵥ x) :=
    (LinearMap.toContinuousLinearMap (Matrix.mulVecLin A)).contDiff.restrict_scalars ℝ
  exact ((hv.comp x hA.contDiffAt).pow 2).div_const 2

theorem abs_maDens_collar_le {n d : ℕ} (g : (Fin n → ℂ) → ℝ) (s : (Fin (d + 1) → ℂ) → Fin n → ℂ)
    (y : Fin (d + 1) → ℂ) (hs : AnalyticAt ℂ s y) (hg : ContDiffAt ℝ 2 g (s y)) {c : ℝ}
    (hb : (hessC g (s y) + (c : ℂ) • 1).PosSemidef ∧ (-hessC g (s y) + (c : ℂ) • 1).PosSemidef) :
    |maDens (fun k => vecCons g (fun _ => euclPot) k ∘ s) y| ≤
      3 ^ (d + 1) * c * maDens (fun _ : Fin (d + 1) => euclPot ∘ s) y := by
  set Jc := ReciprocityTheory.AnForm.A.jacC s y with hJc
  set B := Jc.map (starRingEnd ℂ) with hB
  have hBJ : Bᴴ = Jcᵀ := by
    ext a b
    simp [hB]
  have hE2 : ContDiffAt ℝ 2 (euclPot : (Fin n → ℂ) → ℝ) (s y) :=
    ((contDiff_euclPot n).of_le (WithTop.coe_le_coe.2 le_top)).contDiffAt
  have hH : hessC (g ∘ s) y = Bᴴ * hessC g (s y) * B := by
    rw [hBJ]
    exact ReciprocityTheory.AnForm.A.hessC_comp _ s y hs hg
  have hG : hessC (euclPot ∘ s) y = Bᴴ * B := by
    rw [ReciprocityTheory.AnForm.A.hessC_comp _ s y hs hE2, TubeFormComparison.hessC_euclPot, hBJ, Matrix.mul_one]
  have hGp : (Bᴴ * B).PosSemidef := Matrix.posSemidef_conjTranspose_mul_self B
  set Av : Fin (d + 1) → Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ :=
    fun k => hessC (vecCons g (fun _ => euclPot) k ∘ s) y with hAv
  set a : Fin (d + 1) → ℂ := Fin.cons (c : ℂ) (fun _ => 1) with ha
  set Bv : Fin (d + 1) → Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ := fun k => a k • (Bᴴ * B) with hBv
  have hle : ∀ k, (Bv k - Av k).PosSemidef := by
    intro k
    refine Fin.cases ?_ (fun i => ?_) k
    · simp only [hAv, hBv, ha, Fin.cons_zero, Matrix.cons_val_zero, hH]
      have e : (c : ℂ) • (Bᴴ * B) - Bᴴ * hessC g (s y) * B = Bᴴ * (-hessC g (s y) + (c : ℂ) • 1) * B := by
        simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_smul,
          Matrix.smul_mul, Matrix.mul_one]
        abel
      rw [e]
      exact hb.2.conjTranspose_mul_mul_same B
    · simp only [hAv, hBv, ha, Fin.cons_succ, Matrix.cons_val_succ, hG, one_smul, sub_self]
      exact Matrix.PosSemidef.zero
  have hge : ∀ k, (Av k + Bv k).PosSemidef := by
    intro k
    refine Fin.cases ?_ (fun i => ?_) k
    · simp only [hAv, hBv, ha, Fin.cons_zero, Matrix.cons_val_zero, hH]
      have e : Bᴴ * hessC g (s y) * B + (c : ℂ) • (Bᴴ * B) = Bᴴ * (hessC g (s y) + (c : ℂ) • 1) * B := by
        simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one]
      rw [e]
      exact hb.1.conjTranspose_mul_mul_same B
    · simp only [hAv, hBv, ha, Fin.cons_succ, Matrix.cons_val_succ, hG, one_smul]
      exact hGp.add hGp
  have hmain := ReciprocityTheory.AnForm.A.norm_mdisc_le_of_abs_le Av Bv hle hge
  have hscale : mdisc Bv = (c : ℂ) * mdisc (fun _ : Fin (d + 1) => hessC (euclPot ∘ s) y) := by
    obtain ⟨L, hL⟩ := ReciprocityTheory.AnForm.A.exists_multilinearMap_eq_mdisc (D := d + 1)
    rw [hG, ← hL, hBv, L.map_smul_univ, smul_eq_mul, Fin.prod_univ_succ]
    simp [ha]
  rw [hscale, Complex.re_ofReal_mul] at hmain
  have hm : ∀ Φ : Fin (d + 1) → (Fin (d + 1) → ℂ) → ℝ, maDens Φ y =
      ((d + 1).factorial : ℝ) * (2 / Real.pi) ^ (d + 1) * (mdisc fun k => hessC (Φ k) y).re :=
    fun Φ => rfl
  rw [hm, hm, abs_mul]
  have hK0 : 0 ≤ ((d + 1).factorial : ℝ) * (2 / Real.pi) ^ (d + 1) := by positivity
  rw [abs_of_nonneg hK0]
  calc ((d + 1).factorial : ℝ) * (2 / Real.pi) ^ (d + 1) * |(mdisc Av).re|
      ≤ ((d + 1).factorial : ℝ) * (2 / Real.pi) ^ (d + 1) * ‖mdisc Av‖ := by
        gcongr
        exact Complex.abs_re_le_norm _
    _ ≤ ((d + 1).factorial : ℝ) * (2 / Real.pi) ^ (d + 1) *
        (3 ^ (d + 1) * (c * (mdisc fun _ : Fin (d + 1) => hessC (euclPot ∘ s) y).re)) := by
        gcongr
    _ = _ := by ring

end TubeCollarComparison

open TubeFormComparison TubeCollarComparison in

theorem TubeCollarCompare.proof : TubeCollarCompare.Statement := by
  intro n d J A P R _hJ _hdim hA _hP
  set g : (Fin n → ℂ) → ℝ := fun x => logAbsSq P (A *ᵥ x) ^ 2 / 2 with hgdef
  set U : Set (Fin n → ℂ) := {x | eval (A *ᵥ x) P ≠ 0} with hUdef
  set K : Set (Fin n → ℂ) :=
    Metric.closedBall 0 R ∩ {x | Real.exp (-Real.exp 1) ≤ ‖eval (A *ᵥ x) P‖ ^ 2} with hKdef
  have hcont : Continuous fun x : Fin n → ℂ => eval (A *ᵥ x) P :=
    (MvPolynomial.continuous_eval P).comp (LinearMap.toContinuousLinearMap (Matrix.mulVecLin A)).continuous
  have hU : IsOpen U := isOpen_ne_fun hcont continuous_const
  have hK : IsCompact K :=
    (isCompact_closedBall 0 R).inter_right (isClosed_le continuous_const (hcont.norm.pow 2))
  have hKU : K ⊆ U := fun x hx h0 => by
    have h : Real.exp (-Real.exp 1) ≤ ‖eval (A *ᵥ x) P‖ ^ 2 := hx.2
    rw [h0, norm_zero] at h
    linarith [Real.exp_pos (-Real.exp 1), show (0 : ℝ) ^ 2 = 0 by norm_num]
  have hgU : ContDiffOn ℝ 2 g U := fun x hx => (contDiffAt_logSq_comp A P x hx).contDiffWithinAt
  obtain ⟨c, hc, hb⟩ := exists_hessC_bound (fun _ : Fin 1 => g) K hK (fun _ => U) (fun _ => hU)
    (fun _ => hKU) (fun _ => hgU)
  have hC : 0 ≤ (3 : ℝ) ^ (d + 1) * c := by positivity
  refine ⟨3 ^ (d + 1) * c, fun y => ?_⟩
  by_cases hy : y ∈ {y | -Real.exp 1 ≤ logAbsSq P y}
  swap
  · rw [Set.indicator_of_notMem hy]
    exact mul_nonneg hC (finsum_nonneg fun _ => finsum_nonneg fun _ => by split_ifs <;> positivity)
  rw [Set.indicator_of_mem hy]
  unfold tubeDens chartAbsDens sheetSum
  rw [finsum_mem_eq_finite_toFinset_sum _ (IndefiniteRowSideFullHecke.ComplexSets.fibre_finite hA y),
    finsum_mem_eq_finite_toFinset_sum _ (IndefiniteRowSideFullHecke.ComplexSets.fibre_finite hA y), Finset.mul_sum]
  refine Finset.sum_le_sum fun x hx => ?_
  rw [Set.Finite.mem_toFinset] at hx
  obtain ⟨hxZ, hxy⟩ := hx
  subst hxy
  split_ifs with hsx
  swap
  · simp
  dsimp only
  obtain ⟨V, hV, hyV, hsd, hsx', hsec, -⟩ := hsx.choose_spec
  set s := hsx.choose with hsdef
  set f := (Metric.closedBall (0 : Fin n → ℂ) R).indicator fun x => tubeWeight P (A *ᵥ x) with hfdef
  by_cases hf : f x = 0
  · rw [hf, zero_mul, abs_zero]
    exact mul_nonneg hC (abs_nonneg _)
  have hxB : x ∈ Metric.closedBall (0 : Fin n → ℂ) R := by
    by_contra h
    exact hf (Set.indicator_of_notMem h _)
  have hv1 : logAbsSq P (A *ᵥ x) ≤ -1 := by
    by_contra h
    exact hf (by simp [hfdef, Set.indicator_of_mem hxB, tubeWeight, h])
  have hP : eval (A *ᵥ x) P ≠ 0 := by
    intro h0
    simp [logAbsSq, h0] at hv1
    linarith
  have hxK : x ∈ K := by
    refine ⟨hxB, ?_⟩
    have h2 : 0 < ‖eval (A *ᵥ x) P‖ ^ 2 := by positivity
    have h3 := Real.exp_le_exp.2 (show -Real.exp 1 ≤ logAbsSq P (A *ᵥ x) from hy)
    rwa [logAbsSq, Real.exp_log h2] at h3
  have hw : |f x| ≤ 1 := by
    rw [hfdef, Set.indicator_of_mem hxB]
    simp only [tubeWeight, if_pos hv1]
    rw [abs_of_nonneg (by positivity)]
    exact inv_le_one_of_one_le₀ (by nlinarith)
  have hsa : AnalyticAt ℂ s (A *ᵥ x) :=
    analyticAt_pi_iff.2 fun i =>
      ReciprocityTheory.AnForm.Osgood.osgood _ V (fun z => s z i) hV (differentiableOn_pi.1 hsd i) _ hyV
  have hg2 : ContDiffAt ℝ 2 g (s (A *ᵥ x)) := by
    rw [hsx']
    exact contDiffAt_logSq_comp A P x hP
  have hbx := hb 0 (s (A *ᵥ x)) (by rw [hsx']; exact hxK)
  have key := abs_maDens_collar_le g s (A *ᵥ x) hsa hg2 hbx
  rw [abs_mul, abs_mul, Set.indicator_of_mem hxB, abs_one, one_mul]
  calc |f x| * |maDens (fun k => vecCons g (fun _ => euclPot) k ∘ s) (A *ᵥ x)|
      ≤ 1 * (3 ^ (d + 1) * c * maDens (fun _ : Fin (d + 1) => euclPot ∘ s) (A *ᵥ x)) :=
        mul_le_mul hw key (abs_nonneg _) zero_le_one
    _ ≤ 3 ^ (d + 1) * c * |maDens (fun k => (fun _ : Fin (d + 1) => euclPot) k ∘ s) (A *ᵥ x)| := by
        rw [one_mul]
        exact mul_le_mul_of_nonneg_left (le_abs_self _) hC

end

end GroundTheory.Heights₂.Heights
