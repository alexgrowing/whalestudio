import Mathlib
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.LintegralImageEqLintegralNormSqDetMul
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.MdiscSt
import ReciprocityTheory.AnalyticForms.PotentialTheory.HessCIsHermitian
import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA
import ReciprocityTheory.AnalyticForms.AnalyticCharts.Osgood
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StTubeFormCompare
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.LogIntegrableOnOfLogIntegrable
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Matrix Filter Topology ReciprocityTheory.AnForm ComplexSets
open scoped ContDiff ComplexOrder

noncomputable section

namespace TubeFormComparison

theorem levi_eq_re {N : ℕ} (φ : (Fin N → ℂ) → ℝ) (z a : Fin N → ℂ) :
    levi φ z a = (a ⬝ᵥ (hessC φ z *ᵥ star a)).re := by
  have hq : star (star a) ⬝ᵥ (hessC φ z *ᵥ star a) =
      leviC (fderiv ℝ (fderiv ℝ φ) z) (star (star a)) (star (star a)) := by
    rw [Matrix.dotProduct_mulVec]
    simp only [Matrix.vecMul, dotProduct, hessC_eq_leviC, sum_mul_leviC]
    exact ReciprocityTheory.AnForm.M.sum_leviC_right _ _ _
  rw [star_star] at hq
  rw [hq]
  simp [leviC, levi]

theorem hessC_euclPot {N : ℕ} (z : Fin N → ℂ) : hessC (euclPot : (Fin N → ℂ) → ℝ) z = 1 := by
  have h : (euclPot : (Fin N → ℂ) → ℝ) = fun w => ∑ i, Complex.normSq (w i) := by
    funext w
    simp [euclPot, Complex.normSq_eq_norm_sq]
  rw [h]
  exact ReciprocityTheory.AnForm.A.hessC_sum_normSq z

theorem levi_euclPot {N : ℕ} (z w : Fin N → ℂ) : levi euclPot z w = ∑ j, ‖w j‖ ^ 2 := by
  rw [levi_eq_re, hessC_euclPot, Matrix.one_mulVec]
  simp [dotProduct, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  simp only [← Complex.ofReal_pow, Complex.ofReal_re]

theorem norm_sq_le_sum {N : ℕ} (v : Fin N → ℂ) : ‖v‖ ^ 2 ≤ ∑ j, ‖v j‖ ^ 2 := by
  have hS : 0 ≤ ∑ j, ‖v j‖ ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have h : ‖v‖ ≤ Real.sqrt (∑ j, ‖v j‖ ^ 2) := by
    refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun j => ?_
    exact (le_abs_self _).trans (Real.abs_le_sqrt (Finset.single_le_sum
      (f := fun j => ‖v j‖ ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ j)))
  calc ‖v‖ ^ 2 ≤ Real.sqrt (∑ j, ‖v j‖ ^ 2) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h 2
    _ = _ := Real.sq_sqrt hS

theorem levi_neg {N : ℕ} (φ : (Fin N → ℂ) → ℝ) (z w : Fin N → ℂ) :
    levi (fun y => -φ y) z w = -levi φ z w := by
  have h1 : fderiv ℝ (fun y => -φ y) = -(fderiv ℝ φ) := funext fun y => fderiv_neg
  unfold levi
  rw [h1, fderiv_neg]
  simp only [_root_.neg_apply]
  ring

theorem hessC_neg {N : ℕ} (φ : (Fin N → ℂ) → ℝ) (z : Fin N → ℂ) :
    hessC (fun y => -φ y) z = -hessC φ z := by
  have h : (fun y => -φ y) = fun y => (-1 : ℝ) * φ y := funext fun y => by ring
  rw [h, ReciprocityTheory.AnForm.M.hessC_const_mul']
  simp

theorem posSemidef_hessC_add {N : ℕ} {f : (Fin N → ℂ) → ℝ} {x : Fin N → ℂ} (hf : ContDiffAt ℝ 2 f x)
    {c : ℝ} (hc : 0 ≤ c) (hl : ∀ w, -c * ‖w‖ ^ 2 ≤ levi f x w) :
    (hessC f x + (c : ℂ) • 1).PosSemidef := by
  have hE' : ContDiffAt ℝ 2 (euclPot : (Fin N → ℂ) → ℝ) x :=
    ((contDiff_euclPot N).of_le (WithTop.coe_le_coe.2 le_top)).contDiffAt
  have hE : ContDiffAt ℝ 2 (fun w => c * euclPot w) x := contDiffAt_const.mul hE'
  have e : hessC f x + (c : ℂ) • 1 = hessC (fun w => f w + c * euclPot w) x := by
    rw [ReciprocityTheory.AnForm.M.hessC_add' f _ x hf hE, ReciprocityTheory.AnForm.M.hessC_const_mul', hessC_euclPot]
  rw [e]
  refine ReciprocityTheory.AnForm.M.hessC_posSemidef _ x (hf.add hE) fun w => ?_
  rw [levi_add_smul c hf hE' w, levi_euclPot]
  have h1 := hl w
  have h2 := norm_sq_le_sum w
  nlinarith

theorem exists_hessC_bound {N m : ℕ} (φ : Fin m → (Fin N → ℂ) → ℝ) (K : Set (Fin N → ℂ))
    (hK : IsCompact K) (U : Fin m → Set (Fin N → ℂ)) (hU : ∀ i, IsOpen (U i)) (hKU : ∀ i, K ⊆ U i)
    (hφ : ∀ i, ContDiffOn ℝ 2 (φ i) (U i)) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ i, ∀ x ∈ K, (hessC (φ i) x + (c : ℂ) • 1).PosSemidef ∧
      (-hessC (φ i) x + (c : ℂ) • 1).PosSemidef := by
  have hb : ∀ i, ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ K, ∀ w, |levi (φ i) x w| ≤ C * ‖w‖ ^ 2 := by
    intro i
    have hS : IsCompact (K ×ˢ Metric.sphere (0 : Fin N → ℂ) 1) := hK.prod (isCompact_sphere 0 1)
    obtain ⟨C, hC⟩ := hS.exists_bound_of_continuousOn
      ((continuousOn_levi (hU i) (hφ i)).mono (Set.prod_mono (hKU i) (Set.subset_univ _)))
    refine ⟨max C 0, le_max_right _ _, fun x hx w => ?_⟩
    rcases eq_or_ne w 0 with rfl | hw
    · simp [levi_zero]
    have hn : 0 < ‖w‖ := norm_pos_iff.2 hw
    have hw' : w = ‖w‖ • (‖w‖⁻¹ • w) := by rw [smul_smul, mul_inv_cancel₀ hn.ne', one_smul]
    have hu : ‖‖w‖⁻¹ • w‖ = 1 := by
      rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_norm, inv_mul_cancel₀ hn.ne']
    have hb := hC (x, ‖w‖⁻¹ • w) ⟨hx, mem_sphere_zero_iff_norm.2 hu⟩
    rw [Real.norm_eq_abs] at hb
    calc |levi (φ i) x w| = |levi (φ i) x (‖w‖ • (‖w‖⁻¹ • w))| := by rw [← hw']
      _ = ‖w‖ ^ 2 * |levi (φ i) x (‖w‖⁻¹ • w)| := by
        rw [levi_smul_dir, abs_mul, abs_of_nonneg (sq_nonneg _)]
      _ ≤ ‖w‖ ^ 2 * max C 0 := by gcongr; exact hb.trans (le_max_left _ _)
      _ = _ := by ring
  choose C hC0 hC using hb
  refine ⟨∑ i, C i, Finset.sum_nonneg fun i _ => hC0 i, fun i x hx => ?_⟩
  have hCi : C i ≤ ∑ i, C i := Finset.single_le_sum (fun i _ => hC0 i) (Finset.mem_univ i)
  have hx2 : ContDiffAt ℝ 2 (φ i) x := (hφ i).contDiffAt ((hU i).mem_nhds (hKU i hx))
  have hsum : 0 ≤ ∑ i, C i := Finset.sum_nonneg fun i _ => hC0 i
  refine ⟨posSemidef_hessC_add hx2 hsum fun w => ?_, ?_⟩
  · have h1 := (abs_le.1 (hC i x hx w)).1
    have h2 : 0 ≤ ‖w‖ ^ 2 := sq_nonneg _
    nlinarith
  · rw [← hessC_neg]
    refine posSemidef_hessC_add hx2.neg hsum fun w => ?_
    rw [levi_neg]
    have h1 := (abs_le.1 (hC i x hx w)).2
    have h2 : 0 ≤ ‖w‖ ^ 2 := sq_nonneg _
    nlinarith

theorem levi_sq_half {N : ℕ} {v : (Fin N → ℂ) → ℝ} {y : Fin N → ℂ} (hv : ContDiffAt ℝ 2 v y)
    (w : Fin N → ℂ) :
    levi (fun z => v z ^ 2 / 2) y w =
      ((fderiv ℝ v y w) ^ 2 + (fderiv ℝ v y (Complex.I • w)) ^ 2) / 4 + v y * levi v y w := by
  have hD : HasFDerivAt (fderiv ℝ v) (fderiv ℝ (fderiv ℝ v) y) y :=
    ((hv.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt
  have hev : fderiv ℝ (fun z => v z ^ 2 / 2) =ᶠ[𝓝 y] fun z => v z • fderiv ℝ v z := by
    filter_upwards [hv.eventually (by simp)] with z hz
    have h1 : HasFDerivAt (fun z => v z ^ 2 / 2) (v z • fderiv ℝ v z) z := by
      have h0 := ((hz.differentiableAt (by norm_num)).hasFDerivAt.pow 2).mul_const (1 / 2 : ℝ)
      have e : (fun z => v z ^ 2 / 2) = fun u => v u ^ 2 * (1 / 2) := funext fun u => by ring
      rw [e]
      refine h0.congr_fderiv ?_
      ext u
      simp
      ring
    exact h1.fderiv
  have hv1 : HasFDerivAt v (fderiv ℝ v y) y := (hv.differentiableAt (by norm_num)).hasFDerivAt
  have hF := ((hv1.smul hD).congr_of_eventuallyEq hev).fderiv
  unfold levi
  rw [hF]
  simp
  ring

theorem analyticAt_eval {m : ℕ} (P : MvPolynomial (Fin m) ℂ) (y : Fin m → ℂ) :
    AnalyticAt ℂ (fun z => eval z P) y := by
  have h := AnalyticAt.aeval_mvPolynomial (𝕜 := ℂ) (f := fun z : Fin m → ℂ => z) (z := y)
    (fun i => (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin m => ℂ) i).analyticAt y) P
  simpa [MvPolynomial.coe_aeval_eq_eval] using h

theorem posSemidef_hessC_logSq {m : ℕ} (P : MvPolynomial (Fin m) ℂ) (y : Fin m → ℂ)
    (hP : eval y P ≠ 0) : (hessC (fun z => logAbsSq P z ^ 2 / 2) y).PosSemidef := by
  have hg := analyticAt_eval P y
  have hv : ContDiffAt ℝ 2 (logAbsSq P) y := by
    have h1 : ContDiffAt ℝ 2 (fun z => ‖eval z P‖ ^ 2) y :=
      ((hg.contDiffAt (n := 2)).restrict_scalars ℝ).norm_sq ℝ
    exact h1.log (by positivity)
  have hv0 : hessC (logAbsSq P) y = 0 := by
    have h : logAbsSq P = fun z => (2 : ℝ) * Real.log ‖eval z P‖ := by
      funext z
      rw [logAbsSq, Real.log_pow]
      norm_num
    rw [h, ReciprocityTheory.AnForm.M.hessC_const_mul', ReciprocityTheory.AnForm.A.hessC_log_norm _ y hg hP, smul_zero]
  have hl : ∀ w, levi (logAbsSq P) y w = 0 := fun w => by
    rw [levi_eq_re, hv0]
    simp
  refine ReciprocityTheory.AnForm.M.hessC_posSemidef _ y ((hv.pow 2).div_const 2) fun w => ?_
  rw [levi_sq_half hv w, hl w, mul_zero, add_zero]
  positivity

theorem abs_maDens_cons_le {n d : ℕ} (g : (Fin n → ℂ) → ℝ) (φ : Fin d → (Fin n → ℂ) → ℝ)
    (s : (Fin (d + 1) → ℂ) → Fin n → ℂ) (y : Fin (d + 1) → ℂ) (hs : AnalyticAt ℂ s y)
    (hφ : ∀ i, ContDiffAt ℝ 2 (φ i) (s y)) {c : ℝ}
    (hb : ∀ i, (hessC (φ i) (s y) + (c : ℂ) • 1).PosSemidef ∧
      (-hessC (φ i) (s y) + (c : ℂ) • 1).PosSemidef)
    (hM : (hessC (g ∘ s) y).PosSemidef) :
    |maDens (fun k => vecCons g φ k ∘ s) y| ≤
      3 ^ (d + 1) * c ^ d * maDens (fun k => vecCons g (fun _ => euclPot) k ∘ s) y := by
  set Jc := ReciprocityTheory.AnForm.A.jacC s y with hJc
  set B := Jc.map (starRingEnd ℂ) with hB
  have hBJ : Bᴴ = Jcᵀ := by
    ext a b
    simp [hB]
  have hE2 : ContDiffAt ℝ 2 (euclPot : (Fin n → ℂ) → ℝ) (s y) :=
    ((contDiff_euclPot n).of_le (WithTop.coe_le_coe.2 le_top)).contDiffAt
  have hA : ∀ i, hessC (φ i ∘ s) y = Bᴴ * hessC (φ i) (s y) * B := fun i => by
    rw [hBJ]
    exact ReciprocityTheory.AnForm.A.hessC_comp _ s y hs (hφ i)
  have hG : hessC (euclPot ∘ s) y = Bᴴ * B := by
    rw [ReciprocityTheory.AnForm.A.hessC_comp _ s y hs hE2, hessC_euclPot, hBJ, Matrix.mul_one]
  set M := hessC (g ∘ s) y with hMdef
  set Av : Fin (d + 1) → Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ :=
    fun k => hessC (vecCons g φ k ∘ s) y with hAv
  set Bv : Fin (d + 1) → Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ :=
    Fin.cons M (fun _ => (c : ℂ) • (Bᴴ * B)) with hBv
  have hle : ∀ k, (Bv k - Av k).PosSemidef := by
    intro k
    refine Fin.cases ?_ (fun i => ?_) k
    · simp only [hAv, hBv, Fin.cons_zero, Matrix.cons_val_zero, ← hMdef, sub_self]
      exact Matrix.PosSemidef.zero
    · simp only [hAv, hBv, Fin.cons_succ, Matrix.cons_val_succ, hA]
      have e : (c : ℂ) • (Bᴴ * B) - Bᴴ * hessC (φ i) (s y) * B =
          Bᴴ * (-hessC (φ i) (s y) + (c : ℂ) • 1) * B := by
        simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_neg, Matrix.neg_mul,
          Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one]
        abel
      rw [e]
      exact (hb i).2.conjTranspose_mul_mul_same B
  have hge : ∀ k, (Av k + Bv k).PosSemidef := by
    intro k
    refine Fin.cases ?_ (fun i => ?_) k
    · simp only [hAv, hBv, Fin.cons_zero, Matrix.cons_val_zero, ← hMdef]
      exact hM.add hM
    · simp only [hAv, hBv, Fin.cons_succ, Matrix.cons_val_succ, hA]
      have e : Bᴴ * hessC (φ i) (s y) * B + (c : ℂ) • (Bᴴ * B) =
          Bᴴ * (hessC (φ i) (s y) + (c : ℂ) • 1) * B := by
        simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one]
      rw [e]
      exact (hb i).1.conjTranspose_mul_mul_same B
  have hmain := ReciprocityTheory.AnForm.A.norm_mdisc_le_of_abs_le Av Bv hle hge
  have hscale : mdisc Bv =
      (c : ℂ) ^ d * mdisc (fun k => hessC (vecCons g (fun _ => euclPot) k ∘ s) y) := by
    obtain ⟨L, hL⟩ := ReciprocityTheory.AnForm.A.exists_multilinearMap_eq_mdisc (D := d + 1)
    have e : Bv = fun k => (Fin.cons (1 : ℂ) (fun _ => (c : ℂ)) : Fin (d + 1) → ℂ) k •
        hessC (vecCons g (fun _ => euclPot) k ∘ s) y := by
      funext k
      refine Fin.cases ?_ (fun i => ?_) k
      · simp [hBv, hMdef]
      · simp [hBv, hG]
    rw [e, ← hL, L.map_smul_univ, smul_eq_mul, Fin.prod_univ_succ]
    simp
  rw [hscale, ← Complex.ofReal_pow, Complex.re_ofReal_mul] at hmain
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
        (3 ^ (d + 1) * (c ^ d * (mdisc fun k => hessC (vecCons g (fun _ => euclPot) k ∘ s) y).re)) := by
        gcongr
    _ = _ := by ring

theorem isClosed_zeroSet {n : ℕ} (J : Ideal (MvPolynomial (Fin n) ℂ)) : IsClosed (zeroSet J) := by
  have h : zeroSet J = ⋂ q ∈ J, {x : Fin n → ℂ | eval x q = 0} := by
    ext x
    simp [zeroSet]
  rw [h]
  exact isClosed_biInter fun q _ => isClosed_eq (MvPolynomial.continuous_eval q) continuous_const

end TubeFormComparison

open TubeFormComparison in

theorem TubeFormCompare.proof : TubeFormCompare.Statement := by
  intro n d J A P R φ _hJ _hdim hA hφ
  set K := zeroSet J ∩ Metric.closedBall (0 : Fin n → ℂ) R with hKdef
  have hK : IsCompact K := (isCompact_closedBall 0 R).inter_left (isClosed_zeroSet J)
  choose U hU hZU hφU using hφ
  obtain ⟨c, hc, hb⟩ := exists_hessC_bound φ K hK U hU
    (fun i => Set.inter_subset_left.trans (hZU i)) (fun i => (hφU i).of_le (WithTop.coe_le_coe.2 le_top))
  have hC : 0 ≤ (3 : ℝ) ^ (d + 1) * c ^ d := by positivity
  refine ⟨3 ^ (d + 1) * c ^ d, fun y => ?_⟩
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
  · rw [hf]
    simp
  have hxB : x ∈ Metric.closedBall (0 : Fin n → ℂ) R := by
    by_contra h
    exact hf (Set.indicator_of_notMem h _)
  have hP : eval (A *ᵥ x) P ≠ 0 := by
    intro h0
    apply hf
    simp [hfdef, Set.indicator_of_mem hxB, tubeWeight, logAbsSq, h0]
  have hsa : AnalyticAt ℂ s (A *ᵥ x) :=
    analyticAt_pi_iff.2 fun i =>
      ReciprocityTheory.AnForm.Osgood.osgood _ V (fun z => s z i) hV (differentiableOn_pi.1 hsd i) _ hyV
  have hφx : ∀ i, ContDiffAt ℝ 2 (φ i) (s (A *ᵥ x)) := fun i => by
    rw [hsx']
    exact ((hφU i).contDiffAt ((hU i).mem_nhds (hZU i hxZ))).of_le (WithTop.coe_le_coe.2 le_top)
  have hbx : ∀ i, (hessC (φ i) (s (A *ᵥ x)) + (c : ℂ) • 1).PosSemidef ∧
      (-hessC (φ i) (s (A *ᵥ x)) + (c : ℂ) • 1).PosSemidef := fun i => by
    rw [hsx']
    exact hb i x ⟨hxZ, hxB⟩
  have hgerm : ((fun x => logAbsSq P (A *ᵥ x) ^ 2 / 2) ∘ s) =ᶠ[𝓝 (A *ᵥ x)]
      fun z => logAbsSq P z ^ 2 / 2 := by
    filter_upwards [hV.mem_nhds hyV] with z hz
    simp [(hsec z hz).1]
  have hM : (hessC ((fun x => logAbsSq P (A *ᵥ x) ^ 2 / 2) ∘ s) (A *ᵥ x)).PosSemidef := by
    have e : hessC ((fun x => logAbsSq P (A *ᵥ x) ^ 2 / 2) ∘ s) (A *ᵥ x) =
        hessC (fun z => logAbsSq P z ^ 2 / 2) (A *ᵥ x) := by
      unfold hessC
      rw [(hgerm.fderiv (𝕜 := ℝ)).fderiv_eq (𝕜 := ℝ)]
    rw [e]
    exact posSemidef_hessC_logSq P _ hP
  have key := abs_maDens_cons_le _ φ s (A *ᵥ x) hsa hφx hbx hM
  rw [abs_mul, abs_mul]
  calc |f x| * |maDens (fun k => vecCons (fun x => logAbsSq P (A *ᵥ x) ^ 2 / 2) φ k ∘ s) (A *ᵥ x)|
      ≤ |f x| * (3 ^ (d + 1) * c ^ d *
          |maDens (fun k => vecCons (fun x => logAbsSq P (A *ᵥ x) ^ 2 / 2)
            (fun _ => euclPot) k ∘ s) (A *ᵥ x)|) := by
        gcongr
        exact key.trans (mul_le_mul_of_nonneg_left (le_abs_self _) hC)
    _ = _ := by ring

end

end GroundTheory.Heights₂.Heights
