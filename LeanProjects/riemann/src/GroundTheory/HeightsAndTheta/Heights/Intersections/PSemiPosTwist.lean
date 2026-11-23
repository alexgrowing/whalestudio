import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.NoCommonComponentCoordinatesPlane
import GroundTheory.HeightsAndTheta.Heights.Intersections.StTorusInvLevi
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ArithModel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.ADensStC
import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.LeviOneEqLaplacianThm
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open ReciprocityTheory.ChartRestriction.G.Geo Filter Topology InnerProductSpace Laplacian

namespace SemipositiveTwist

set_option linter.unusedSectionVars false

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

def F (k : K) (y : (Σ k, ι k) → ℂ) : ℝ :=
  Real.log ((fsMetric (ι k)).ρ (fun i => y ⟨k, i⟩))

theorem blk_ne {z : (Σ k, ι k) → ℂ} (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) (k : K) :
    (fun i => z ⟨k, i⟩ : ι k → ℂ) ≠ 0 := by
  obtain ⟨i, hi⟩ := hz k
  exact fun h0 => hi (congrFun h0 i)

theorem rho_pos {z : (Σ k, ι k) → ℂ} (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) (k : K) :
    0 < (fsMetric (ι k)).ρ (fun i => z ⟨k, i⟩) :=
  (fsMetric (ι k)).pos _ (blk_ne hz k)

theorem rho_eq (k : K) (y : (Σ k, ι k) → ℂ) :
    (fsMetric (ι k)).ρ (fun i => y ⟨k, i⟩) = Real.sqrt (∑ i, ‖y ⟨k, i⟩‖ ^ 2) := by
  simp [fsMetric, EuclideanSpace.norm_eq]

theorem contDiffAt_F {z : (Σ k, ι k) → ℂ} (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) (k : K) :
    ContDiffAt ℝ 2 (F k) z := by
  have hφ := ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.adens_contDiffAt_logρ_id
    (GroundTheory.Heights₂.Heights.HilbertSamuel.ProjLine.isSmoothMetric_fs (J := ι k)) (blk_ne hz k)
  have hFk : F k = (fun u => Real.log ((fsMetric (ι k)).ρ u)) ∘ blk (ι := ι) k := rfl
  rw [hFk]
  exact hφ.comp z ((blk (ι := ι) k).restrictScalars ℝ).contDiff.contDiffAt

theorem levi_F_nonneg {z : (Σ k, ι k) → ℂ} (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) (k : K)
    (w : (Σ k, ι k) → ℂ) : 0 ≤ ReciprocityTheory.AnForm.levi (F k) z w := by
  have hφ := ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.adens_contDiffAt_logρ_id
    (GroundTheory.Heights₂.Heights.HilbertSamuel.ProjLine.isSmoothMetric_fs (J := ι k)) (blk_ne hz k)
  have hFk : F k = (fun u => Real.log ((fsMetric (ι k)).ρ u)) ∘ blk (ι := ι) k := rfl
  rw [hFk, ReciprocityTheory.AnForm.levi_comp w ((blk (ι := ι) k).analyticAt z) hφ]
  exact GroundTheory.Heights₂.Heights.HilbertSamuel.ProjLine.leviForm_log_fs_nonneg (blk_ne hz k) _

end Blocks

section Levi

variable {J : Type} [Fintype J]

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

theorem levi_zero_fun (z w : J → ℂ) : ReciprocityTheory.AnForm.levi (fun _ : J → ℂ => (0 : ℝ)) z w = 0 := by
  simp [ReciprocityTheory.AnForm.levi]

theorem laplacian_line_eq_levi {φ : (J → ℂ) → ℝ} {z : J → ℂ} (hφ : ContDiffAt ℝ 2 φ z) (v : J → ℂ) :
    Δ (fun t : ℂ => φ (z + t • v)) 0 = 4 * ReciprocityTheory.AnForm.levi φ z v := by
  have h1 : ReciprocityTheory.AnForm.levi (fun w : Fin 1 → ℂ => φ (z + w 0 • v)) (fun _ => 0) (Pi.single 0 1) =
      Δ (fun t : ℂ => φ (z + t • v)) 0 / 4 :=
    ReciprocityTheory.AnForm.A.leviOne (fun t : ℂ => φ (z + t • v)) 0
  set L : (Fin 1 → ℂ) →L[ℂ] (J → ℂ) :=
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 1 => ℂ) 0).smulRight v with hL
  have hτ : AnalyticAt ℂ (fun w => z + L w) (fun _ => 0) :=
    analyticAt_const.add (L.analyticAt _)
  have hτ0 : z + L (fun _ => (0 : ℂ)) = z := by
    simp [hL]
  have hcomp : (fun w : Fin 1 → ℂ => φ (z + w 0 • v)) = φ ∘ fun w => z + L w := by
    funext w
    simp [hL]
  have hD : fderiv ℂ (fun w => z + L w) (fun _ => 0) (Pi.single 0 1) = v := by
    rw [((L.hasFDerivAt).const_add z).fderiv]
    simp [hL]
  have hφ' : ContDiffAt ℝ 2 φ (z + L (fun _ => 0)) := by
    rw [hτ0]
    exact hφ
  rw [hcomp, ReciprocityTheory.AnForm.levi_comp _ hτ hφ', hτ0, hD] at h1
  linarith

end Levi

end SemipositiveTwist

open SemipositiveTwist in

theorem SemiPosTwist.proof (hB : TorusInvLevi.Statement) : SemiPosTwist.Statement := by
  intro K _ ι _ M hM
  classical
  have hUo := isOpen_noZeroBlock (ι := ι)
  set u : ((Σ k, ι k) → ℂ) → ℝ := fun y => Real.log (M.h y) + ∑ k, (-(M.a k : ℝ)) * F k y with hu
  have hlogM : ∀ z : (Σ k, ι k) → ℂ, (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) →
      ContDiffAt ℝ 2 (fun y => Real.log (M.h y)) z := fun z hz =>
    ((hM.contDiffAt (hUo.mem_nhds hz)).of_le (WithTop.coe_le_coe.2 le_top)).log (M.pos z hz).ne'
  have hu2 : ∀ z : (Σ k, ι k) → ℂ, (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → ContDiffAt ℝ 2 u z := fun z hz =>
    (levi_add_sum _ F (fun k => -(M.a k : ℝ)) (hlogM z hz) (contDiffAt_F hz) 0 Finset.univ).1

  have hinv : ∀ (c : K → ℂ) (z : (Σ k, ι k) → ℂ), (∀ k, c k ≠ 0) → (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) →
      u (fun p => c p.1 * z p) = u z := by
    intro c z hc hz
    have hcn : ∀ k, ‖c k‖ ≠ 0 := fun k => norm_ne_zero_iff.mpr (hc k)
    have hF : ∀ k, F k (fun p => c p.1 * z p) = Real.log ‖c k‖ + F k z := by
      intro k
      show Real.log ((fsMetric (ι k)).ρ (c k • fun i => z ⟨k, i⟩)) =
        Real.log ‖c k‖ + Real.log ((fsMetric (ι k)).ρ (fun i => z ⟨k, i⟩))
      rw [(fsMetric (ι k)).smul, Real.log_mul (hcn k) (rho_pos hz k).ne']
    have hh : Real.log (M.h (fun p => c p.1 * z p)) =
        ∑ k, (M.a k : ℝ) * Real.log ‖c k‖ + Real.log (M.h z) := by
      rw [M.smul c z hc, Real.log_mul (Finset.prod_ne_zero_iff.mpr fun k _ => zpow_ne_zero _ (hcn k))
        (M.pos z hz).ne', Real.log_prod (fun k _ => zpow_ne_zero _ (hcn k))]
      simp only [Real.log_zpow]
    rw [hu]
    show Real.log (M.h (fun p => c p.1 * z p)) + ∑ k, (-(M.a k : ℝ)) * F k (fun p => c p.1 * z p) =
      Real.log (M.h z) + ∑ k, (-(M.a k : ℝ)) * F k z
    rw [hh]
    simp only [hF, mul_add, Finset.sum_add_distrib, neg_mul, Finset.sum_neg_distrib]
    ring
  obtain ⟨C, hC⟩ := hB K ι u (fun z hz => (hu2 z hz).contDiffWithinAt) hinv

  have hΦ : ∀ z : (Σ k, ι k) → ℂ, (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → ∀ w,
      leviForm (fun y => ∑ k, Real.log ((fsMetric (ι k)).ρ (fun i => y ⟨k, i⟩))) z w =
        ∑ k, ReciprocityTheory.AnForm.levi (F k) z w := by
    intro z hz w
    have h := (levi_add_sum (fun _ => (0 : ℝ)) F (fun _ => 1) contDiffAt_const (contDiffAt_F hz) w
      Finset.univ).2
    simp only [zero_add, one_mul, levi_zero_fun] at h
    exact h

  set N : ℕ := ⌈|C| + ∑ k, |(M.a k : ℝ)|⌉₊ with hN
  have hNk : ∀ k, C ≤ (M.a k : ℝ) + N := by
    intro k
    have h1 : |C| + ∑ k, |(M.a k : ℝ)| ≤ N := Nat.le_ceil _
    have h2 : |(M.a k : ℝ)| ≤ ∑ k, |(M.a k : ℝ)| :=
      Finset.single_le_sum (f := fun k => |(M.a k : ℝ)|) (fun _ _ => abs_nonneg _) (Finset.mem_univ k)
    have h3 := le_abs_self C
    have h4 := neg_abs_le (M.a k : ℝ)
    linarith
  set T : HermLine ι := HermLine.sqMetric (fun _ => N) with hT
  have hlogT : ∀ y : (Σ k, ι k) → ℂ, (∀ k, ∃ i, y ⟨k, i⟩ ≠ 0) →
      Real.log (T.h y) = ∑ k, (N : ℝ) * F k y := by
    intro y hy
    have h : T.h y = ∏ k, (fsMetric (ι k)).ρ (fun i => y ⟨k, i⟩) ^ N := by
      simp only [hT, HermLine.sqMetric, rho_eq]
    rw [h, Real.log_prod (fun k _ => pow_ne_zero _ (rho_pos hy k).ne')]
    simp only [Real.log_pow, F]
  refine ⟨T, isSmoothHerm_sqMetric _, ?_, ?_⟩
  · intro z hz v
    have hs := levi_add_sum (fun _ => (0 : ℝ)) F (fun _ => (N : ℝ)) contDiffAt_const (contDiffAt_F hz) v
      Finset.univ
    beta_reduce at hs
    have hev : (fun y => Real.log (T.h y)) =ᶠ[𝓝 z] fun y => 0 + ∑ k, (N : ℝ) * F k y := by
      filter_upwards [hUo.mem_nhds hz] with y hy
      rw [hlogT y hy, zero_add]
    rw [laplacian_line_eq_levi (hs.1.congr_of_eventuallyEq hev) v, ReciprocityTheory.AnForm.levi_congr hev v,
      hs.2, levi_zero_fun, zero_add]
    exact mul_nonneg (by norm_num) (Finset.sum_nonneg fun k _ =>
      mul_nonneg (Nat.cast_nonneg _) (levi_F_nonneg hz k v))
  · intro z hz v
    have hs := levi_add_sum u F (fun k => (M.a k : ℝ) + N) (hu2 z hz) (contDiffAt_F hz) v Finset.univ
    beta_reduce at hs
    have hev : (fun y => Real.log ((M.tensor T).h y)) =ᶠ[𝓝 z]
        fun y => u y + ∑ k, ((M.a k : ℝ) + N) * F k y := by
      filter_upwards [hUo.mem_nhds hz] with y hy
      show Real.log (M.h y * T.h y) = _
      rw [Real.log_mul (M.pos y hy).ne' (T.pos y hy).ne', hlogT y hy, hu]
      simp only [add_mul, neg_mul, Finset.sum_add_distrib, Finset.sum_neg_distrib]
      ring
    rw [laplacian_line_eq_levi (hs.1.congr_of_eventuallyEq hev) v, ReciprocityTheory.AnForm.levi_congr hev v, hs.2]
    have hC' : |ReciprocityTheory.AnForm.levi u z v| ≤ C * ∑ k, ReciprocityTheory.AnForm.levi (F k) z v := by
      rw [← hΦ z hz v]
      exact hC z hz v
    have hsum : 0 ≤ ∑ k, ((M.a k : ℝ) + N - C) * ReciprocityTheory.AnForm.levi (F k) z v :=
      Finset.sum_nonneg fun k _ => mul_nonneg (by linarith [hNk k]) (levi_F_nonneg hz k v)
    have hexp : ∑ k, ((M.a k : ℝ) + N) * ReciprocityTheory.AnForm.levi (F k) z v =
        ∑ k, ((M.a k : ℝ) + N - C) * ReciprocityTheory.AnForm.levi (F k) z v +
          C * ∑ k, ReciprocityTheory.AnForm.levi (F k) z v := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun k _ => by ring
    have h5 := neg_abs_le (ReciprocityTheory.AnForm.levi u z v)
    linarith

end GroundTheory.Heights₂.Heights.Inter
