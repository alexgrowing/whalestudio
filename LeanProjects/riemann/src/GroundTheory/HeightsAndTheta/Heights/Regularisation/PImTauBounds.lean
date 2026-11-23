import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Regularisation.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Regular

open Metric Matrix Filter Topology

noncomputable section

theorem quad_smul {g : ℕ} (M : Matrix (Fin g) (Fin g) ℝ) (t : ℝ) (v : Fin g → ℝ) :
    (t • v) ⬝ᵥ M *ᵥ (t • v) = t ^ 2 * (v ⬝ᵥ M *ᵥ v) := by
  rw [Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]; ring

theorem dot_self_nonneg {g : ℕ} (v : Fin g → ℝ) : 0 ≤ v ⬝ᵥ v :=
  Finset.sum_nonneg fun i _ => mul_self_nonneg (v i)

def unitSphereDot (g : ℕ) : Set (Fin g → ℝ) := {u | u ⬝ᵥ u = 1}

theorem isCompact_unitSphereDot (g : ℕ) : IsCompact (unitSphereDot g) := by
  have hc : IsClosed (unitSphereDot g) :=
    isClosed_eq (continuous_id.dotProduct continuous_id) continuous_const
  refine (isCompact_closedBall (0 : Fin g → ℝ) 1).of_isClosed_subset hc ?_
  intro u hu
  have hu' : u ⬝ᵥ u = 1 := hu
  rw [mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg zero_le_one]
  intro i
  rw [Real.norm_eq_abs, abs_le_one_iff_mul_self_le_one]
  have : u i * u i ≤ u ⬝ᵥ u :=
    Finset.single_le_sum (f := fun j => u j * u j) (fun j _ => mul_self_nonneg (u j))
      (Finset.mem_univ i)
  linarith

theorem exists_unit_of_ne_zero {g : ℕ} {v : Fin g → ℝ} (hv : v ≠ 0) :
    ∃ u ∈ unitSphereDot g, ∀ M : Matrix (Fin g) (Fin g) ℝ,
      v ⬝ᵥ M *ᵥ v = (v ⬝ᵥ v) * (u ⬝ᵥ M *ᵥ u) := by
  have hpos : 0 < v ⬝ᵥ v :=
    lt_of_le_of_ne (dot_self_nonneg v) (fun h => hv (dotProduct_self_eq_zero.mp h.symm))
  set s := Real.sqrt (v ⬝ᵥ v) with hs
  have hs0 : 0 < s := Real.sqrt_pos.mpr hpos
  have hs2 : s ^ 2 = v ⬝ᵥ v := Real.sq_sqrt hpos.le
  have hvu : v = s • (s⁻¹ • v) := by rw [smul_smul, mul_inv_cancel₀ hs0.ne', one_smul]
  refine ⟨s⁻¹ • v, ?_, fun M => ?_⟩
  · show (s⁻¹ • v) ⬝ᵥ (s⁻¹ • v) = 1
    have := quad_smul (1 : Matrix (Fin g) (Fin g) ℝ) s⁻¹ v
    rw [one_mulVec, one_mulVec] at this
    rw [this, ← hs2]; field_simp
  · conv_lhs => rw [hvu]
    rw [quad_smul, hs2]

theorem quad_upper_core {Z : Type*} [TopologicalSpace Z] {g : ℕ} {K : Set Z} (hK : IsCompact K)
    (M : Z → Matrix (Fin g) (Fin g) ℝ) (hM : ContinuousOn M K) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ z ∈ K, ∀ v : Fin g → ℝ, v ⬝ᵥ M z *ᵥ v ≤ A * (v ⬝ᵥ v) := by
  have hΦ : Continuous fun q : Matrix (Fin g) (Fin g) ℝ × (Fin g → ℝ) => q.2 ⬝ᵥ q.1 *ᵥ q.2 :=
    continuous_snd.dotProduct (continuous_fst.matrix_mulVec continuous_snd)
  have hc : ContinuousOn (fun p : Z × (Fin g → ℝ) => p.2 ⬝ᵥ M p.1 *ᵥ p.2)
      (K ×ˢ unitSphereDot g) :=
    hΦ.comp_continuousOn ((hM.comp continuous_fst.continuousOn fun p hp => hp.1).prodMk
      continuous_snd.continuousOn)
  obtain ⟨A, hA⟩ := (hK.prod (isCompact_unitSphereDot g)).exists_bound_of_continuousOn hc
  refine ⟨max A 0, le_max_right _ _, fun z hz v => ?_⟩
  by_cases hv : v = 0
  · subst hv; simp
  obtain ⟨u, hu, huM⟩ := exists_unit_of_ne_zero hv
  rw [huM]
  have h1 := hA (z, u) ⟨hz, hu⟩
  have h2 : u ⬝ᵥ M z *ᵥ u ≤ max A 0 :=
    ((le_abs_self _).trans (by simpa [Real.norm_eq_abs] using h1)).trans (le_max_left _ _)
  rw [mul_comm]
  exact mul_le_mul_of_nonneg_right h2 (dot_self_nonneg v)

theorem quad_lower_core {Z : Type*} [TopologicalSpace Z] {g : ℕ} {K W : Set Z}
    (hK : IsCompact K) (hW : IsOpen W) (hKW : K ⊆ W)
    (M : Z → Matrix (Fin g) (Fin g) ℝ) (hM : ContinuousOn M W)
    (S : Matrix (Fin g) (Fin g) ℝ) (hS : S.PosSemidef)
    (hpos : ∀ z ∈ K, ∀ v : Fin g → ℝ, v ≠ 0 → S *ᵥ v = 0 → 0 < v ⬝ᵥ M z *ᵥ v) :
    ∃ L ε : ℝ, 0 < ε ∧ ∀ z ∈ K, ∀ v : Fin g → ℝ,
      ε * (v ⬝ᵥ v) ≤ L * (v ⬝ᵥ S *ᵥ v) + v ⬝ᵥ M z *ᵥ v := by
  have hSnn : ∀ v : Fin g → ℝ, 0 ≤ v ⬝ᵥ S *ᵥ v := fun v => by
    simpa using (posSemidef_iff_dotProduct_mulVec.mp hS).2 v
  have hΦ : Continuous fun q : Matrix (Fin g) (Fin g) ℝ × (Fin g → ℝ) => q.2 ⬝ᵥ q.1 *ᵥ q.2 :=
    continuous_snd.dotProduct (continuous_fst.matrix_mulVec continuous_snd)
  let F : ℕ → Z × (Fin g → ℝ) → ℝ := fun m p =>
    (m : ℝ) * (p.2 ⬝ᵥ S *ᵥ p.2) + p.2 ⬝ᵥ M p.1 *ᵥ p.2
  have hFc : ∀ m, ContinuousOn (F m) (W ×ˢ Set.univ) := by
    intro m
    have hQ : ContinuousOn (fun p : Z × (Fin g → ℝ) => p.2 ⬝ᵥ M p.1 *ᵥ p.2) (W ×ˢ Set.univ) :=
      hΦ.comp_continuousOn ((hM.comp continuous_fst.continuousOn fun p hp => hp.1).prodMk
        continuous_snd.continuousOn)
    have hS' : Continuous fun p : Z × (Fin g → ℝ) => p.2 ⬝ᵥ S *ᵥ p.2 :=
      continuous_snd.dotProduct (continuous_const.matrix_mulVec continuous_snd)
    exact (continuous_const.mul hS').continuousOn.add hQ
  let U : ℕ → Set (Z × (Fin g → ℝ)) := fun m =>
    (W ×ˢ Set.univ) ∩ F m ⁻¹' Set.Ioi (1 / ((m : ℝ) + 1))
  have hUo : ∀ m, IsOpen (U m) := fun m =>
    (hFc m).isOpen_inter_preimage (hW.prod isOpen_univ) isOpen_Ioi
  have hmono : Monotone U := by
    intro m m' hmm' p hp
    refine ⟨hp.1, ?_⟩
    have hp2 : 1 / ((m : ℝ) + 1) < F m p := hp.2
    have hmm : (m : ℝ) ≤ m' := Nat.cast_le.mpr hmm'
    have h1 : F m p ≤ F m' p := by
      have := hSnn p.2
      show (m : ℝ) * (p.2 ⬝ᵥ S *ᵥ p.2) + _ ≤ (m' : ℝ) * (p.2 ⬝ᵥ S *ᵥ p.2) + _
      nlinarith
    have h2 : 1 / ((m' : ℝ) + 1) ≤ 1 / ((m : ℝ) + 1) := by gcongr
    show 1 / ((m' : ℝ) + 1) < F m' p
    linarith
  have hcover : K ×ˢ unitSphereDot g ⊆ ⋃ m, U m := by
    rintro ⟨z, u⟩ ⟨hz, hu⟩
    have hu' : u ⬝ᵥ u = 1 := hu
    have hu0 : u ≠ 0 := by rintro rfl; simp at hu'
    simp only [Set.mem_iUnion]
    have hm0 : ∀ m : ℕ, (0 : ℝ) ≤ m := fun m => Nat.cast_nonneg m
    by_cases hSu : S *ᵥ u = 0
    · have hQ := hpos z hz u hu0 hSu
      obtain ⟨m, hm⟩ := exists_nat_one_div_lt hQ
      refine ⟨m, ⟨⟨hKW hz, trivial⟩, ?_⟩⟩
      show 1 / ((m : ℝ) + 1) < (m : ℝ) * (u ⬝ᵥ S *ᵥ u) + u ⬝ᵥ M z *ᵥ u
      have := hSnn u
      nlinarith [hm0 m]
    · have hs : 0 < u ⬝ᵥ S *ᵥ u := by
        refine lt_of_le_of_ne (hSnn u) (fun h => hSu ?_)
        have := (hS.dotProduct_mulVec_zero_iff u).mp
        simp only [star_trivial] at this
        exact this h.symm
      obtain ⟨m, hm⟩ := exists_nat_gt ((1 - u ⬝ᵥ M z *ᵥ u) / (u ⬝ᵥ S *ᵥ u))
      refine ⟨m, ⟨⟨hKW hz, trivial⟩, ?_⟩⟩
      show 1 / ((m : ℝ) + 1) < (m : ℝ) * (u ⬝ᵥ S *ᵥ u) + u ⬝ᵥ M z *ᵥ u
      have h1 : 1 - u ⬝ᵥ M z *ᵥ u < (m : ℝ) * (u ⬝ᵥ S *ᵥ u) := by rwa [div_lt_iff₀ hs] at hm
      have h2 : 1 / ((m : ℝ) + 1) ≤ 1 := by
        rw [div_le_one (by positivity)]; linarith [hm0 m]
      linarith
  obtain ⟨m, hm⟩ := (hK.prod (isCompact_unitSphereDot g)).elim_directed_cover U hUo hcover
    hmono.directed_le
  refine ⟨m, 1 / ((m : ℝ) + 1), by positivity, fun z hz v => ?_⟩
  by_cases hv : v = 0
  · subst hv; simp
  obtain ⟨u, hu, huM⟩ := exists_unit_of_ne_zero hv
  have hp : 1 / ((m : ℝ) + 1) < F m (z, u) := (hm ⟨hz, hu⟩).2
  have hvv := dot_self_nonneg v
  rw [huM S, huM (M z)]
  have h := mul_le_mul_of_nonneg_left hp.le hvv
  simp only [F] at h
  nlinarith [h]

namespace PeriodPolydisc

variable {n a g : ℕ} (P : PeriodPolydisc n a g)

def realB (i : Fin a) : Matrix (Fin g) (Fin g) ℝ := (P.B i).map (Int.cast : ℤ → ℝ)

theorem im_tau_eq {T0 : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ} (hT0 : P.IsTau0Ext T0)
    {w : Fin n → ℂ} (hw : w ∈ logCover P.a_le) :
    (P.τ w).map Complex.im = (T0 (expCover a w)).map Complex.im +
      ∑ i : Fin a, (-(w (Fin.castLE P.a_le i)).re / (2 * Real.pi)) • P.realB i := by
  have hτ : P.τ w = T0 (expCover a w) + ∑ i : Fin a,
      (w (Fin.castLE P.a_le i) / (2 * Real.pi * Complex.I)) • (P.B i).map (Int.cast : ℤ → ℂ) := by
    rw [← hT0.2 w hw, PeriodPolydisc.tau0, sub_add_cancel]
  ext p q
  rw [hτ]
  simp [Matrix.sum_apply, Complex.im_sum, Complex.mul_im, im_div_two_pi_I, realB]

end PeriodPolydisc

theorem quad_add_sum {g a : ℕ} (A : Matrix (Fin g) (Fin g) ℝ) (l : Fin a → ℝ)
    (B : Fin a → Matrix (Fin g) (Fin g) ℝ) (v : Fin g → ℝ) :
    v ⬝ᵥ (A + ∑ i, l i • B i) *ᵥ v = v ⬝ᵥ A *ᵥ v + ∑ i, l i * (v ⬝ᵥ B i *ᵥ v) := by
  rw [Matrix.add_mulVec, dotProduct_add, Matrix.sum_mulVec, dotProduct_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]

theorem ImTauBounds.proof (h0 : Tau0Holomorphic.Statement) (h1 : KernelPositive.Statement) :
    ImTauBounds.Statement := by
  intro n a g P
  obtain ⟨hB, T0, hT0⟩ := h0 n a g P
  have hBpsd : ∀ i, (P.realB i).PosSemidef := hB
  have hBnn : ∀ i (v : Fin g → ℝ), 0 ≤ v ⬝ᵥ P.realB i *ᵥ v := fun i v => by
    simpa using (posSemidef_iff_dotProduct_mulVec.mp (hBpsd i)).2 v
  set S := ∑ i, P.realB i with hSdef
  have hSv : ∀ v : Fin g → ℝ, v ⬝ᵥ S *ᵥ v = ∑ i, v ⬝ᵥ P.realB i *ᵥ v := fun v => by
    rw [hSdef, Matrix.sum_mulVec, dotProduct_sum]
  have hS : S.PosSemidef := posSemidef_sum Finset.univ fun i _ => hBpsd i
  set Mz : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℝ := fun z => (T0 z).map Complex.im with hMz
  have hMc : ContinuousOn Mz (ball 0 1) := by
    refine continuousOn_pi.mpr fun p => continuousOn_pi.mpr fun q => ?_
    exact Complex.continuous_im.comp_continuousOn (hT0.1 p q).continuousOn
  have hK : IsCompact (closedBall (0 : Fin n → ℂ) (1 / 2)) := isCompact_closedBall _ _
  have hKW : closedBall (0 : Fin n → ℂ) (1 / 2) ⊆ ball 0 1 :=
    closedBall_subset_ball (by norm_num)
  have hpos : ∀ z ∈ closedBall (0 : Fin n → ℂ) (1 / 2), ∀ v : Fin g → ℝ, v ≠ 0 →
      S *ᵥ v = 0 → 0 < v ⬝ᵥ Mz z *ᵥ v := by
    intro z hz v hv hSv0
    refine h1 n a g P T0 hT0 v hv (fun i => ?_) z (hKW hz)
    have h := hSv v
    rw [hSv0, dotProduct_zero] at h
    have hi := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hBnn j v)).mp h.symm i
      (Finset.mem_univ i)
    have := ((hBpsd i).dotProduct_mulVec_zero_iff v).mp
    simp only [star_trivial] at this
    exact this hi
  obtain ⟨L, ε, hε, hlow⟩ := quad_lower_core hK isOpen_ball hKW Mz hMc S hS hpos
  obtain ⟨A, hA0, hA⟩ := quad_upper_core hK Mz (hMc.mono hKW)
  have hBup : ∀ i, ∃ β : ℝ, 0 ≤ β ∧ ∀ v : Fin g → ℝ,
      v ⬝ᵥ P.realB i *ᵥ v ≤ β * (v ⬝ᵥ v) := by
    intro i
    obtain ⟨β, hβ0, hβ⟩ := quad_upper_core hK (fun _ => P.realB i) continuousOn_const
    exact ⟨β, hβ0, hβ 0 (mem_closedBall_self (by norm_num))⟩
  choose β hβ0 hβ using hBup
  refine ⟨min (1 / 2) (Real.exp (-(2 * Real.pi) * L)), ε, A + ∑ i, β i,
    lt_min (by norm_num) (Real.exp_pos _), lt_of_le_of_lt (min_le_left _ _) (by norm_num), hε, ?_⟩
  intro w hw hz
  have hzK : expCover a w ∈ closedBall (0 : Fin n → ℂ) (1 / 2) :=
    closedBall_subset_closedBall (min_le_left _ _) hz
  have hdec := P.im_tau_eq hT0 hw
  set z := expCover a w with hzdef
  set l : Fin a → ℝ := fun i => -(w (Fin.castLE P.a_le i)).re / (2 * Real.pi) with hl
  have hquad : ∀ v : Fin g → ℝ, v ⬝ᵥ (P.τ w).map Complex.im *ᵥ v =
      v ⬝ᵥ Mz z *ᵥ v + ∑ i, l i * (v ⬝ᵥ P.realB i *ᵥ v) := by
    intro v; rw [hdec]; exact quad_add_sum _ _ _ v
  have hzi : ∀ i : Fin a, z (Fin.castLE P.a_le i) = Complex.exp (w (Fin.castLE P.a_le i)) := by
    intro i; simp [hzdef, expCover, i.isLt]
  have hre : ∀ i : Fin a, (w (Fin.castLE P.a_le i)).re < 0 := hw.1
  have hnorm : ∀ i : Fin a,
      Real.exp (w (Fin.castLE P.a_le i)).re ≤ Real.exp (-(2 * Real.pi) * L) := by
    intro i
    have h1 : ‖z (Fin.castLE P.a_le i)‖ ≤ ‖z‖ := norm_le_pi_norm z _
    have h2 : ‖z‖ ≤ min (1 / 2) (Real.exp (-(2 * Real.pi) * L)) := by
      simpa [mem_closedBall, dist_zero_right] using hz
    rw [hzi, Complex.norm_exp] at h1
    exact h1.trans (h2.trans (min_le_right _ _))
  have hlL : ∀ i, L ≤ l i := by
    intro i
    have := Real.exp_le_exp.mp (hnorm i)
    show L ≤ -(w (Fin.castLE P.a_le i)).re / (2 * Real.pi)
    rw [le_div_iff₀ (by positivity)]
    linarith
  have hterm : ∀ j : Fin a,
      Real.log (‖cuspCoord P.a_le z j‖ ^ 2)⁻¹ = -2 * (w (Fin.castLE P.a_le j)).re := by
    intro j
    rw [cuspCoord, hzi, Complex.norm_exp, Real.log_inv, Real.log_pow, Real.log_exp]
    push_cast; ring
  have hsum0 : 0 ≤ ∑ j, Real.log (‖cuspCoord P.a_le z j‖ ^ 2)⁻¹ :=
    Finset.sum_nonneg fun j _ => by rw [hterm j]; linarith [hre j]
  have hr1 : 1 ≤ chartRadius P.a_le z := by
    rw [chartRadius]
    have he : 1 ≤ Real.exp 1 := by have := Real.add_one_le_exp 1; linarith
    linarith
  have hlr : ∀ i, l i ≤ chartRadius P.a_le z := by
    intro i
    rw [chartRadius]
    have hsum : -2 * (w (Fin.castLE P.a_le i)).re ≤
        ∑ j, Real.log (‖cuspCoord P.a_le z j‖ ^ 2)⁻¹ := by
      rw [← hterm i]
      exact Finset.single_le_sum (f := fun j => Real.log (‖cuspCoord P.a_le z j‖ ^ 2)⁻¹)
        (fun j _ => by rw [hterm j]; linarith [hre j]) (Finset.mem_univ i)
    have hli : l i ≤ -2 * (w (Fin.castLE P.a_le i)).re := by
      show -(w (Fin.castLE P.a_le i)).re / (2 * Real.pi) ≤ _
      rw [div_le_iff₀ (by positivity)]
      have := hre i
      nlinarith [Real.pi_gt_three]
    have he : 0 ≤ Real.exp 1 := (Real.exp_pos 1).le
    linarith
  have hsymm : ((P.τ w).map Complex.im)ᵀ = (P.τ w).map Complex.im := by
    rw [← Matrix.transpose_map, P.symm w hw]
  refine ⟨?_, ?_⟩
  · rw [posSemidef_iff_dotProduct_mulVec]
    refine ⟨?_, fun v => ?_⟩
    · rw [IsHermitian, conjTranspose_eq_transpose_of_trivial, transpose_sub, transpose_smul,
        transpose_one, hsymm]
    · simp only [star_trivial, sub_mulVec, smul_mulVec, one_mulVec, dotProduct_sub,
        dotProduct_smul, smul_eq_mul]
      rw [hquad]
      have h1 := hlow z hzK v
      rw [hSv, Finset.mul_sum] at h1
      have h2 : ∑ i, L * (v ⬝ᵥ P.realB i *ᵥ v) ≤ ∑ i, l i * (v ⬝ᵥ P.realB i *ᵥ v) :=
        Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hlL i) (hBnn i v)
      linarith
  · rw [posSemidef_iff_dotProduct_mulVec]
    refine ⟨?_, fun v => ?_⟩
    · rw [IsHermitian, conjTranspose_eq_transpose_of_trivial, transpose_sub, transpose_smul,
        transpose_one, hsymm]
    · simp only [star_trivial, sub_mulVec, smul_mulVec, one_mulVec, dotProduct_sub,
        dotProduct_smul, smul_eq_mul]
      rw [hquad]
      have hvv := dot_self_nonneg v
      have h1 := hA z hzK v
      have h2 : ∑ i, l i * (v ⬝ᵥ P.realB i *ᵥ v) ≤
          ∑ i, chartRadius P.a_le z * (β i * (v ⬝ᵥ v)) :=
        Finset.sum_le_sum fun i _ => mul_le_mul (hlr i) (hβ i v) (hBnn i v) (by linarith)
      have h3 : ∑ i, chartRadius P.a_le z * (β i * (v ⬝ᵥ v)) =
          chartRadius P.a_le z * (∑ i, β i) * (v ⬝ᵥ v) := by
        rw [Finset.mul_sum, Finset.sum_mul]
        exact Finset.sum_congr rfl fun i _ => by ring
      have h4 : A * (v ⬝ᵥ v) ≤ A * chartRadius P.a_le z * (v ⬝ᵥ v) := by
        have := mul_le_mul_of_nonneg_left hr1 (mul_nonneg hA0 hvv)
        nlinarith
      nlinarith

end

end GroundTheory.Heights₂.Heights.Regular
