import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.StTorusInvLevi
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.CoordinateIdeals.FubiniLevi
import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open ReciprocityTheory.ChartRestriction.G.Geo Filter Topology
open GroundTheory.Heights₂.Heights.LowerBoundFree.FubiniLevi

namespace TorusInvariantLevi

set_option linter.unusedSectionVars false

section Vectors

variable {J : Type} [Fintype J]

theorem sum_sum_normSq_cross (z w : J → ℂ) :
    ∑ j, ∑ l, ‖z j * w l - z l * w j‖ ^ 2 =
      2 * (sqSum z * sqSum w - (reInner z w ^ 2 + reInner z (Complex.I • w) ^ 2)) := by
  set B : J → ℝ := fun j => (z j).re * (w j).re + (z j).im * (w j).im with hB
  set D : J → ℝ := fun j => (z j).re * (w j).im - (z j).im * (w j).re with hD
  have hterm : ∀ j l, ‖z j * w l - z l * w j‖ ^ 2 =
      ‖z j‖ ^ 2 * ‖w l‖ ^ 2 + ‖z l‖ ^ 2 * ‖w j‖ ^ 2 - 2 * (B j * B l + D j * D l) := by
    intro j l
    simp only [hB, hD, Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
      Complex.mul_re, Complex.mul_im]
    ring
  have e1 : sqSum z * sqSum w = ∑ j, ∑ l, ‖z j‖ ^ 2 * ‖w l‖ ^ 2 := by
    rw [sqSum, sqSum, Finset.sum_mul_sum]
  have e2 : sqSum z * sqSum w = ∑ j, ∑ l, ‖z l‖ ^ 2 * ‖w j‖ ^ 2 := by
    rw [mul_comm, sqSum, sqSum, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => mul_comm _ _
  have e3 : reInner z w ^ 2 = ∑ j, ∑ l, B j * B l := by
    rw [reInner_apply, sq, Finset.sum_mul_sum]
  have e4 : reInner z (Complex.I • w) ^ 2 = ∑ j, ∑ l, D j * D l := by
    rw [reInner_apply, sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
    simp only [hD, Pi.smul_apply, smul_eq_mul, Complex.mul_re, Complex.mul_im, Complex.I_re,
      Complex.I_im]
    ring
  have hsplit : ∑ j, ∑ l, (‖z j‖ ^ 2 * ‖w l‖ ^ 2 + ‖z l‖ ^ 2 * ‖w j‖ ^ 2 - 2 * (B j * B l + D j * D l)) =
      ∑ j, ∑ l, ‖z j‖ ^ 2 * ‖w l‖ ^ 2 + ∑ j, ∑ l, ‖z l‖ ^ 2 * ‖w j‖ ^ 2 -
        2 * (∑ j, ∑ l, B j * B l + ∑ j, ∑ l, D j * D l) := by
    simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.mul_sum, mul_add]
  rw [Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => hterm j l, hsplit, ← e1, ← e2,
    ← e3, ← e4]
  ring

theorem row_le (z w : J → ℂ) (q : J) :
    ∑ l, ‖z q * w l - z l * w q‖ ^ 2 ≤ ∑ j, ∑ l, ‖z j * w l - z l * w j‖ ^ 2 :=
  Finset.single_le_sum (f := fun j => ∑ l, ‖z j * w l - z l * w j‖ ^ 2)
    (fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) (Finset.mem_univ q)

theorem sum_cross_eq_levi {z : J → ℂ} (hS : sqSum z ≠ 0) (w : J → ℂ) :
    ∑ j, ∑ l, ‖z j * w l - z l * w j‖ ^ 2 = 4 * sqSum z ^ 2 * leviForm phi z w := by
  rw [sum_sum_normSq_cross, leviForm_phi hS w]
  field_simp
  ring

theorem leviForm_phi_nonneg {z : J → ℂ} (hS : sqSum z ≠ 0) (w : J → ℂ) : 0 ≤ leviForm phi z w := by
  have h0 : 0 ≤ ∑ j, ∑ l, ‖z j * w l - z l * w j‖ ^ 2 :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  rw [sum_cross_eq_levi hS w] at h0
  have hS2 : 0 < 4 * sqSum z ^ 2 := by positivity
  exact (mul_nonneg_iff_of_pos_left hS2).1 h0

theorem chart_bound {z w : J → ℂ} {q : J} (hq : ∀ j, ‖z j‖ ≤ ‖z q‖) (hz : z q ≠ 0) :
    ∑ l, ‖(z q * w l - z l * w q) / z q ^ 2‖ ^ 2 ≤ 4 * (Fintype.card J : ℝ) ^ 2 * leviForm phi z w := by
  have ha : 0 < ‖z q‖ ^ 2 := pow_pos (norm_pos_iff.2 hz) 2
  have hSq : ‖z q‖ ^ 2 ≤ sqSum z :=
    Finset.single_le_sum (f := fun j => ‖z j‖ ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ q)
  have hS : sqSum z ≠ 0 := (lt_of_lt_of_le ha hSq).ne'
  have hSle : sqSum z ≤ Fintype.card J * ‖z q‖ ^ 2 := by
    calc sqSum z = ∑ j, ‖z j‖ ^ 2 := rfl
      _ ≤ ∑ _j : J, ‖z q‖ ^ 2 :=
        Finset.sum_le_sum fun j _ => pow_le_pow_left₀ (norm_nonneg _) (hq j) 2
      _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hL := leviForm_phi_nonneg hS w
  have hrow := row_le z w q
  rw [sum_cross_eq_levi hS w] at hrow
  have hterm : ∀ l, ‖(z q * w l - z l * w q) / z q ^ 2‖ ^ 2 =
      ‖z q * w l - z l * w q‖ ^ 2 / (‖z q‖ ^ 2) ^ 2 := by
    intro l
    rw [norm_div, norm_pow, div_pow]
  rw [Finset.sum_congr rfl fun l _ => hterm l, ← Finset.sum_div, div_le_iff₀ (by positivity)]
  have h2 : sqSum z ^ 2 ≤ (Fintype.card J * ‖z q‖ ^ 2) ^ 2 :=
    pow_le_pow_left₀ (sqSum_nonneg z) hSle 2
  calc _ ≤ 4 * sqSum z ^ 2 * leviForm phi z w := hrow
    _ ≤ 4 * (Fintype.card J * ‖z q‖ ^ 2) ^ 2 * leviForm phi z w := by gcongr
    _ = _ := by ring

theorem levi_bound_compact {φ : (J → ℂ) → ℝ} {U Q : Set (J → ℂ)} (hU : IsOpen U) (hφ : ContDiffOn ℝ 2 φ U)
    (hQ : IsCompact Q) (hQU : Q ⊆ U) :
    ∃ M, 0 ≤ M ∧ ∀ x ∈ Q, ∀ v, |ReciprocityTheory.AnForm.levi φ x v| ≤ M * (‖v‖ * ‖v‖) := by
  have hc := ReciprocityTheory.AnForm.continuousOn_levi hU hφ
  have hK : IsCompact (Q ×ˢ Metric.sphere (0 : J → ℂ) 1) := hQ.prod (isCompact_sphere 0 1)
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn
    (hc.mono (Set.prod_mono hQU (Set.subset_univ _)))
  refine ⟨max M 0, le_max_right _ _, fun x hx v => ?_⟩
  rcases eq_or_ne v 0 with rfl | hv
  · simp [ReciprocityTheory.AnForm.levi_zero]
  have hn : 0 < ‖v‖ := norm_pos_iff.2 hv
  set v' : J → ℂ := (‖v‖⁻¹ : ℝ) • v with hv'def
  have hv' : v = (‖v‖ : ℝ) • v' := by
    rw [hv'def, smul_smul, mul_inv_cancel₀ hn.ne', one_smul]
  have hv'n : ‖v'‖ = 1 := by
    rw [hv'def, norm_smul, Real.norm_eq_abs, abs_inv, abs_norm, inv_mul_cancel₀ hn.ne']
  have hb : |ReciprocityTheory.AnForm.levi φ x v'| ≤ M := by
    simpa [Real.norm_eq_abs] using hM (x, v') ⟨hx, mem_sphere_zero_iff_norm.2 hv'n⟩
  calc |ReciprocityTheory.AnForm.levi φ x v| = |ReciprocityTheory.AnForm.levi φ x ((‖v‖ : ℝ) • v')| := by rw [← hv']
    _ = ‖v‖ ^ 2 * |ReciprocityTheory.AnForm.levi φ x v'| := by
      rw [ReciprocityTheory.AnForm.levi_smul_dir, abs_mul, abs_of_nonneg (sq_nonneg _)]
    _ ≤ ‖v‖ ^ 2 * max M 0 := by gcongr; exact hb.trans (le_max_left _ _)
    _ = _ := by ring

theorem norm_mul_self_le_sum (v : J → ℂ) : ‖v‖ * ‖v‖ ≤ ∑ p, ‖v p‖ ^ 2 := by
  have hS : 0 ≤ ∑ p, ‖v p‖ ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have h : ‖v‖ ≤ Real.sqrt (∑ p, ‖v p‖ ^ 2) := by
    refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun p => ?_
    exact (le_abs_self _).trans (Real.abs_le_sqrt (Finset.single_le_sum (f := fun p => ‖v p‖ ^ 2)
      (fun _ _ => sq_nonneg _) (Finset.mem_univ p)))
  calc ‖v‖ * ‖v‖ ≤ Real.sqrt (∑ p, ‖v p‖ ^ 2) * Real.sqrt (∑ p, ‖v p‖ ^ 2) :=
        mul_self_le_mul_self (norm_nonneg _) h
    _ = _ := Real.mul_self_sqrt hS

theorem log_rho_eq_phi (x : J → ℂ) : Real.log ((fsMetric J).ρ x) = phi x := by
  have h : (fsMetric J).ρ x = Real.sqrt (sqSum x) := by
    simp [fsMetric, EuclideanSpace.norm_eq, sqSum]
  rw [h, Real.log_sqrt (sqSum_nonneg x), phi]
  ring

theorem levi_add_sum {K : Type} {z : J → ℂ} (g : (J → ℂ) → ℝ) (f : K → (J → ℂ) → ℝ) (c : K → ℝ)
    (hg : ContDiffAt ℝ 2 g z) (hf : ∀ k, ContDiffAt ℝ 2 (f k) z) (w : J → ℂ) (s : Finset K) :
    ContDiffAt ℝ 2 (fun y => g y + ∑ k ∈ s, c k * f k y) z ∧
      ReciprocityTheory.AnForm.levi (fun y => g y + ∑ k ∈ s, c k * f k y) z w =
        ReciprocityTheory.AnForm.levi g z w + ∑ k ∈ s, c k * ReciprocityTheory.AnForm.levi (f k) z w := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hg
  | insert a s ha ih =>
    have heq : (fun y => g y + ∑ k ∈ insert a s, c k * f k y) =
        fun y => (fun y' => g y' + ∑ k ∈ s, c k * f k y') y + c a * f a y := by
      funext y
      rw [Finset.sum_insert ha]
      ring
    rw [heq, ReciprocityTheory.AnForm.levi_add_smul (c a) ih.1 (hf a) w, ih.2, Finset.sum_insert ha]
    exact ⟨ih.1.add (contDiffAt_const.mul (hf a)), by ring⟩

end Vectors

section Blocks

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem isOpen_noZeroBlock : IsOpen {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := by
  have h : {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} = ⋂ k, ⋃ i, {z | z ⟨k, i⟩ ≠ 0} := by
    ext z
    simp
  rw [h]
  exact isOpen_iInter_of_finite fun k => isOpen_iUnion fun i =>
    isOpen_ne_fun (continuous_apply _) continuous_const

def blk (k : K) : ((Σ k, ι k) → ℂ) →L[ℂ] (ι k → ℂ) :=
  ContinuousLinearMap.pi fun i =>
    ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : (Σ k, ι k) => ℂ) ⟨k, i⟩

theorem levi_Phi {z : (Σ k, ι k) → ℂ} (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) (w : (Σ k, ι k) → ℂ) :
    leviForm (fun y => ∑ k, Real.log ((fsMetric (ι k)).ρ (fun i => y ⟨k, i⟩))) z w =
      ∑ k, leviForm phi (blk k z) (blk k w) := by
  have hS : ∀ k, sqSum (blk k z) ≠ 0 := by
    intro k
    obtain ⟨i, hi⟩ := hz k
    refine (lt_of_lt_of_le (pow_pos (norm_pos_iff.2 hi) 2) ?_).ne'
    exact Finset.single_le_sum (f := fun j => ‖blk k z j‖ ^ 2) (fun _ _ => sq_nonneg _)
      (Finset.mem_univ i)
  have hf : ∀ k, ContDiffAt ℝ 2 (phi ∘ blk (ι := ι) k) z := fun k =>
    (contDiffAt_phi (hS k)).comp z ((blk (ι := ι) k).restrictScalars ℝ).contDiff.contDiffAt
  have hfun : (fun y => ∑ k, Real.log ((fsMetric (ι k)).ρ (fun i => y ⟨k, i⟩))) =
      fun y => (fun _ => (0 : ℝ)) y + ∑ k ∈ Finset.univ, (fun _ => (1 : ℝ)) k * (phi ∘ blk (ι := ι) k) y := by
    funext y
    simp only [zero_add, one_mul, Function.comp_apply]
    exact Finset.sum_congr rfl fun k _ => log_rho_eq_phi _
  have h := (levi_add_sum (fun _ => (0 : ℝ)) (fun k => phi ∘ blk (ι := ι) k) (fun _ => 1)
    contDiffAt_const hf w Finset.univ).2
  show ReciprocityTheory.AnForm.levi _ z w = _
  rw [hfun, h]
  have h0 : ReciprocityTheory.AnForm.levi (fun _ : (Σ k, ι k) → ℂ => (0 : ℝ)) z w = 0 := by
    simp [ReciprocityTheory.AnForm.levi]
  rw [h0, zero_add]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [one_mul, ReciprocityTheory.AnForm.levi_comp w ((blk (ι := ι) k).analyticAt z) (contDiffAt_phi (hS k)),
    ContinuousLinearMap.fderiv]
  rfl

end Blocks

end TorusInvariantLevi

open TorusInvariantLevi in

theorem TorusInvLevi.proof : TorusInvLevi.Statement := by
  intro K _ ι _ u hu hinv
  have hUo := isOpen_noZeroBlock (ι := ι)
  set U := {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} with hUdef

  set Q : Set ((Σ k, ι k) → ℂ) := Metric.closedBall 0 1 ∩ {x | ∀ k, ∃ j, x ⟨k, j⟩ = 1} with hQ
  have hQc : IsCompact Q := by
    have hcl : IsClosed {x : (Σ k, ι k) → ℂ | ∀ k, ∃ j, x ⟨k, j⟩ = 1} := by
      have h : {x : (Σ k, ι k) → ℂ | ∀ k, ∃ j, x ⟨k, j⟩ = 1} = ⋂ k, ⋃ j, {x | x ⟨k, j⟩ = 1} := by
        ext x
        simp
      rw [h]
      exact isClosed_iInter fun k => isClosed_iUnion_of_finite fun j =>
        isClosed_eq (continuous_apply _) continuous_const
    exact (isCompact_closedBall 0 1).inter_right hcl
  have hQU : Q ⊆ U := fun x hx k => by
    obtain ⟨j, hj⟩ := hx.2 k
    exact ⟨j, by rw [hj]; exact one_ne_zero⟩
  obtain ⟨M, hM0, hM⟩ := levi_bound_compact hUo hu hQc hQU
  set B : ℝ := ∑ k, 4 * (Fintype.card (ι k) : ℝ) ^ 2 with hB
  refine ⟨M * B, fun z hz w => ?_⟩

  have hmax : ∀ k, ∃ j, ∀ j', ‖z ⟨k, j'⟩‖ ≤ ‖z ⟨k, j⟩‖ := fun k => by
    obtain ⟨j0, _⟩ := hz k
    obtain ⟨j, _, hj⟩ := Finset.exists_max_image Finset.univ (fun j => ‖z ⟨k, j⟩‖)
      ⟨j0, Finset.mem_univ _⟩
    exact ⟨j, fun j' => hj j' (Finset.mem_univ _)⟩
  choose i hi using hmax
  have hne : ∀ k, z ⟨k, i k⟩ ≠ 0 := fun k => by
    obtain ⟨j0, hj0⟩ := hz k
    intro h0
    have h := hi k j0
    rw [h0, norm_zero] at h
    exact hj0 (norm_le_zero_iff.1 h)
  set τ : ((Σ k, ι k) → ℂ) → ((Σ k, ι k) → ℂ) := fun y p => y p * (y ⟨p.1, i p.1⟩)⁻¹ with hτdef
  have hτa : AnalyticAt ℂ τ z := analyticAt_pi_iff.2 fun p =>
    ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : (Σ k, ι k) => ℂ) p).analyticAt z).mul
      (((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : (Σ k, ι k) => ℂ) ⟨p.1, i p.1⟩).analyticAt
        z).inv (hne p.1))
  have hτQ : τ z ∈ Q := by
    refine ⟨?_, fun k => ⟨i k, ?_⟩⟩
    · rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg zero_le_one]
      rintro ⟨k, j⟩
      simp only [hτdef, norm_mul, norm_inv]
      rw [mul_inv_le_iff₀ (norm_pos_iff.2 (hne k)), one_mul]
      exact hi k j
    · simp only [hτdef]
      exact mul_inv_cancel₀ (hne k)

  have hev : u ∘ τ =ᶠ[𝓝 z] u := by
    have hV : IsOpen {y : (Σ k, ι k) → ℂ | ∀ k, y ⟨k, i k⟩ ≠ 0} := by
      have h : {y : (Σ k, ι k) → ℂ | ∀ k, y ⟨k, i k⟩ ≠ 0} = ⋂ k, {y | y ⟨k, i k⟩ ≠ 0} := by
        ext y
        simp
      rw [h]
      exact isOpen_iInter_of_finite fun k => isOpen_ne_fun (continuous_apply _) continuous_const
    filter_upwards [hV.mem_nhds hne] with y hy
    have h := hinv (fun k => (y ⟨k, i k⟩)⁻¹) y (fun k => inv_ne_zero (hy k)) (fun k => ⟨i k, hy k⟩)
    simp only [Function.comp_apply, hτdef]
    rw [← h]
    congr 1
    funext p
    ring
  have hu' : ContDiffAt ℝ 2 u (τ z) := hu.contDiffAt (hUo.mem_nhds (hQU hτQ))
  have hlevi : leviForm u z w = ReciprocityTheory.AnForm.levi u (τ z) (fderiv ℂ τ z w) := by
    show ReciprocityTheory.AnForm.levi u z w = _
    rw [← ReciprocityTheory.AnForm.levi_congr hev w, ReciprocityTheory.AnForm.levi_comp w hτa hu']

  have hD : ∀ p, fderiv ℂ τ z w p =
      (z ⟨p.1, i p.1⟩ * w p - z p * w ⟨p.1, i p.1⟩) / z ⟨p.1, i p.1⟩ ^ 2 := by
    intro p
    have hinvq : ∀ q : (Σ k, ι k), z q ≠ 0 → HasFDerivAt (fun y : (Σ k, ι k) → ℂ => (y q)⁻¹) _ z :=
      fun q hq => (hasFDerivAt_inv hq).comp z (hasFDerivAt_apply (𝕜 := ℂ) q z)
    have hc : ∀ p : (Σ k, ι k), HasFDerivAt (fun y : (Σ k, ι k) → ℂ => y p * (y ⟨p.1, i p.1⟩)⁻¹) _ z :=
      fun p => (hasFDerivAt_apply (𝕜 := ℂ) p z).mul (hinvq _ (hne p.1))
    have key : fderiv ℂ τ z = ContinuousLinearMap.pi fun p =>
        fderiv ℂ (fun y : (Σ k, ι k) → ℂ => y p * (y ⟨p.1, i p.1⟩)⁻¹) z :=
      fderiv_pi fun p => (hc p).differentiableAt
    rw [key, ContinuousLinearMap.pi_apply, (hc p).fderiv]
    have hq := hne p.1
    simp
    field_simp
    ring

  have hS : ∀ k, sqSum (blk k z) ≠ 0 := by
    intro k
    refine (lt_of_lt_of_le (pow_pos (norm_pos_iff.2 (hne k)) 2) ?_).ne'
    exact Finset.single_le_sum (f := fun j => ‖blk k z j‖ ^ 2) (fun _ _ => sq_nonneg _)
      (Finset.mem_univ (i k))
  have hLnn : ∀ k, 0 ≤ leviForm phi (blk k z) (blk k w) := fun k => leviForm_phi_nonneg (hS k) _
  have hblock : ∀ k, ∑ l, ‖fderiv ℂ τ z w ⟨k, l⟩‖ ^ 2 ≤
      4 * (Fintype.card (ι k) : ℝ) ^ 2 * leviForm phi (blk k z) (blk k w) := by
    intro k
    calc _ = ∑ l, ‖(blk k z (i k) * blk k w l - blk k z l * blk k w (i k)) / blk k z (i k) ^ 2‖ ^ 2 :=
          Finset.sum_congr rfl fun l _ => by rw [hD]; rfl
      _ ≤ _ := chart_bound (fun j => hi k j) (hne k)
  have hv := hM (τ z) hτQ (fderiv ℂ τ z w)
  have hsup := norm_mul_self_le_sum (fderiv ℂ τ z w)
  have hsplit : ∑ p, ‖fderiv ℂ τ z w p‖ ^ 2 = ∑ k, ∑ l, ‖fderiv ℂ τ z w ⟨k, l⟩‖ ^ 2 :=
    Fintype.sum_sigma _
  rw [hlevi, levi_Phi hz w]
  calc _ ≤ M * (‖fderiv ℂ τ z w‖ * ‖fderiv ℂ τ z w‖) := hv
    _ ≤ M * ∑ k, ∑ l, ‖fderiv ℂ τ z w ⟨k, l⟩‖ ^ 2 := by
      rw [← hsplit]
      exact mul_le_mul_of_nonneg_left hsup hM0
    _ ≤ M * ∑ k, 4 * (Fintype.card (ι k) : ℝ) ^ 2 * leviForm phi (blk k z) (blk k w) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun k _ => hblock k) hM0
    _ ≤ M * ∑ k, B * leviForm phi (blk k z) (blk k w) := by
      refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun k _ => ?_) hM0
      refine mul_le_mul_of_nonneg_right ?_ (hLnn k)
      exact Finset.single_le_sum (f := fun k => 4 * (Fintype.card (ι k) : ℝ) ^ 2)
        (fun _ _ => by positivity) (Finset.mem_univ k)
    _ = M * B * ∑ k, leviForm phi (blk k z) (blk k w) := by
      rw [← Finset.mul_sum]
      ring

end GroundTheory.Heights₂.Heights.Inter
