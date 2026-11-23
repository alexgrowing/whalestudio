import Mathlib
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsLiftGraphFactor
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PLiftGraphMetric
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PPowerBlockMetric
import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter Topology
open GroundTheory.Heights₂.Heights.HilbertSamuel

noncomputable section

set_option linter.unusedSectionVars false

namespace LiftGraphFactor

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

def blkNorm (w : (Σ k, ι k) → ℂ) (k : K) : ℝ := Real.sqrt (∑ i, ‖w ⟨k, i⟩‖ ^ 2)

theorem blkSq_pos {w : (Σ k, ι k) → ℂ} (hw : ∀ k, ∃ i, w ⟨k, i⟩ ≠ 0) (k : K) :
    0 < ∑ i, ‖w ⟨k, i⟩‖ ^ 2 := by
  obtain ⟨i, hi⟩ := hw k
  exact lt_of_lt_of_le (pow_pos (norm_pos_iff.2 hi) 2)
    (Finset.single_le_sum (f := fun i => ‖w ⟨k, i⟩‖ ^ 2) (fun _ _ => by positivity) (Finset.mem_univ i))

theorem blkNorm_pos {w : (Σ k, ι k) → ℂ} (hw : ∀ k, ∃ i, w ⟨k, i⟩ ≠ 0) (k : K) : 0 < blkNorm w k :=
  Real.sqrt_pos.2 (blkSq_pos hw k)

theorem blkNorm_smul (c : K → ℂ) (w : (Σ k, ι k) → ℂ) (k : K) :
    blkNorm (fun p => c p.1 * w p) k = ‖c k‖ * blkNorm w k := by
  unfold blkNorm
  have : ∑ i, ‖c k * w ⟨k, i⟩‖ ^ 2 = ‖c k‖ ^ 2 * ∑ i, ‖w ⟨k, i⟩‖ ^ 2 := by
    simp only [norm_mul, mul_pow, Finset.mul_sum]
  rw [this, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)]

theorem blkNorm_conj (w : (Σ k, ι k) → ℂ) (k : K) :
    blkNorm (fun p => (starRingEnd ℂ) (w p)) k = blkNorm w k := by
  simp [blkNorm]

def fsLineZ (n : K → ℤ) : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι where
  a := n
  h w := ∏ k, blkNorm w k ^ n k
  pos w hw := Finset.prod_pos fun k _ => zpow_pos (blkNorm_pos hw k) _
  smul c w hc := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [blkNorm_smul, mul_zpow]

theorem contDiffAt_zpow_of_ne {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → ℝ} {x : E}
    {N : WithTop ℕ∞} (hf : ContDiffAt ℝ N f x) (hx : f x ≠ 0) (m : ℤ) :
    ContDiffAt ℝ N (fun y => f y ^ m) x := by
  cases m with
  | ofNat k =>
    simp only [Int.ofNat_eq_natCast, zpow_natCast]
    exact hf.pow k
  | negSucc k =>
    simp only [zpow_negSucc]
    exact (hf.pow (k + 1)).inv (pow_ne_zero _ hx)

theorem isSmoothHerm_fsLineZ (n : K → ℤ) : IsSmoothHerm (fsLineZ (ι := ι) n) := by
  intro w hw
  refine ContDiffAt.contDiffWithinAt ?_
  show ContDiffAt ℝ _ (fun x => ∏ k, blkNorm x k ^ n k) w
  refine contDiffAt_prod (t := Finset.univ) (f := fun k x => blkNorm x k ^ n k) fun k _ => ?_
  refine contDiffAt_zpow_of_ne (f := fun x => blkNorm x k) ?_ (blkNorm_pos hw k).ne' (n k)
  have hs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : (Σ k, ι k) → ℂ => ∑ i, ‖x ⟨k, i⟩‖ ^ 2) :=
    ContDiff.sum fun i _ => (contDiff_norm_sq ℝ).comp (contDiff_apply ℝ ℂ _)
  exact hs.contDiffAt.sqrt (blkSq_pos hw k).ne'

theorem conj_fsLineZ (n : K → ℤ) : IsConjInvariantH (fsLineZ (ι := ι) n) := by
  intro w
  show ∏ k, blkNorm _ k ^ n k = ∏ k, blkNorm w k ^ n k
  simp only [blkNorm_conj]

end LiftGraphFactor

open LiftGraphFactor in

theorem LiftGraphFactor.proof (hExt : SectionNormSqExtension.Statement) : LiftGraphFactor.Statement := by
  intro K _ _ ι _ Ω _ y N a r v hv hgen
  classical
  let A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι := fsLineZ (a • N.a)
  have hA1 : ∀ j, v j ∈ chartLat y A.a 1 := hv
  have hgen' : KH.GeneratesOn y (fun k => ((1 : ℕ) : ℤ) * A.a k) v := by
    have e : (fun k => ((1 : ℕ) : ℤ) * A.a k) = a • N.a := by
      funext k
      simp [A, fsLineZ]
    rw [e]
    exact hgen
  obtain ⟨S, hSs, hSp, hSt, hSc, hSv, hSl⟩ :=
    hExt K ι Ω y A 1 r v (isSmoothHerm_fsLineZ _) (conj_fsLineZ _) hA1 hgen'
  let U0 : Set ((Σ k, ι k) → ℂ) := {w | ∀ k, ∃ i, w ⟨k, i⟩ ≠ 0}
  have hAs : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) A.h U0 := isSmoothHerm_fsLineZ _
  refine ⟨fun w => S w * A.h w ^ 2, hSs.mul (hAs.pow 2), fun w hw => mul_pos (hSp w hw) (pow_pos (A.pos w hw) 2),
    ?_, ?_, ?_, ?_⟩
  ·
    intro c w hc hw
    show S _ * A.h _ ^ 2 = _ * (S w * A.h w ^ 2)
    rw [hSt c w hc, A.smul c w hc]
    have hAa : A.a = a • N.a := rfl
    rw [hAa]
    ring
  ·
    intro w
    show S _ * A.h _ ^ 2 = S w * A.h w ^ 2
    rw [hSc w, conj_fsLineZ _ w]
  ·
    intro z hz j
    have hx := PowerBlockMetric.oldPart_mem hz
    obtain ⟨c, hc⟩ := PowerBlockMetric.graph_prop (A := A) (m := 1) hA1 hgen' hz
    have hvN : ∀ j, v j ∈ chartLat y N.a a := by
      intro j c' hc'
      have h := hv j c' hc'
      have e : ∀ k, -(((1 : ℕ) : ℤ) * (a • N.a) k) = -((a : ℤ) * N.a k) := fun k => by
        simp [Pi.smul_apply]
      simp only [e] at h
      exact h

    have key : ∀ j, secNormAt y N a (v j) (basePart₂ z) * N.h (basePart₂ z) ^ a =
        ‖PowerBlockMetric.val y A 1 (v j) (basePart₂ z)‖ * A.h (basePart₂ z) := by
      intro j
      obtain ⟨⟨g, h⟩, hr, hne⟩ := PowerBlockMetric.exists_rep_at (hA1 j) hx
      have hrN : PowerBlockMetric.IsRep y N.a a (v j) g h := by
        obtain ⟨dg, dh, hg, hh, hd, hy⟩ := hr
        refine ⟨dg, dh, hg, hh, fun k => ?_, hy⟩
        rw [hd k]
        simp [A, fsLineZ, Pi.smul_apply]
      have eA := PowerBlockMetric.val_spec (hA1 j) hx hr
      have eN := PowerBlockMetric.val_spec (hvN j) hx hrN
      have hNp : 0 < N.h (basePart₂ z) := N.pos _ hx.1
      have hAp : 0 < A.h (basePart₂ z) := A.pos _ hx.1
      have e2 : PowerBlockMetric.val y N a (v j) (basePart₂ z) * (N.h (basePart₂ z) : ℂ) ^ a =
          PowerBlockMetric.val y A 1 (v j) (basePart₂ z) * (A.h (basePart₂ z) : ℂ) := by
        apply mul_right_cancel₀ hne
        have := eN.symm.trans eA
        simp only [pow_one] at this
        linear_combination this
      rw [PowerBlockMetric.secNormAt_eq (hvN j) hx]
      have := congrArg norm e2
      simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hNp.le,
        Real.norm_of_nonneg hAp.le] at this
      exact this
    have hS : S (basePart₂ z) = ∑ i, ‖PowerBlockMetric.val y A 1 (v i) (basePart₂ z)‖ ^ 2 := by
      rw [hSv _ hx]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [PowerBlockMetric.secNormAt_eq (hA1 i) hx]
    have hN : ∑ i : Fin r, ‖z ⟨none, i⟩‖ ^ 2 = ‖c‖ ^ 2 * S (basePart₂ z) := by
      rw [hS, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hc i, norm_mul, mul_pow]
    have hSp' : 0 ≤ S (basePart₂ z) := (hSp _ hx.1).le
    have hAp : 0 < A.h (basePart₂ z) := A.pos _ hx.1
    rw [key j, hN, hc j, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg _),
      Real.sqrt_mul hSp', Real.sqrt_sq hAp.le, norm_mul]
    ring
  ·
    intro z hz ξ hξ
    have hx := PowerBlockMetric.oldPart_mem hz
    have hw : basePart₂ z ∈ U0 := hx.1
    have hU0o : IsOpen U0 := LiftGraphMetric.isOpen_allNZ
    have hUo : IsOpen {z : (Σ k, addIdx ι r k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := LiftGraphMetric.isOpen_allNZ
    have h2le : (2 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ ⊤)
    have hoR : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : (Σ k, addIdx ι r k) → ℂ => basePart₂ z) :=
      ((LiftGraphMetric.oldCLM (ι := ι) r).restrictScalars ℝ).contDiff
    have hSlog : ContDiffAt ℝ 2 (fun w => Real.log (S w)) (basePart₂ z) :=
      ((hSs.contDiffAt (hU0o.mem_nhds hw)).of_le h2le).log (hSp _ hw).ne'
    have hAlog : ContDiffAt ℝ 2 (fun w => Real.log (A.h w)) (basePart₂ z) :=
      ((hAs.contDiffAt (hU0o.mem_nhds hw)).of_le h2le).log (A.pos _ hw).ne'
    have hL1 : ContDiffAt ℝ 2 (fun x : (Σ k, addIdx ι r k) → ℂ => Real.log (∑ i : Fin r, ‖x ⟨none, i⟩‖ ^ 2)) z :=
      (PowerBlockMetric.contDiff_newSq.contDiffAt).log (PowerBlockMetric.newSq_pos hz.1).ne'
    have hL2 : ContDiffAt ℝ 2 (fun x : (Σ k, addIdx ι r k) → ℂ => Real.log (S (basePart₂ x))) z :=
      hSlog.comp z (hoR.contDiffAt.of_le h2le)
    have hL3 : ContDiffAt ℝ 2 (fun x : (Σ k, addIdx ι r k) → ℂ => Real.log (A.h (basePart₂ x))) z :=
      hAlog.comp z (hoR.contDiffAt.of_le h2le)
    have hcomp : ReciprocityTheory.AnForm.levi (fun x => Real.log (A.h (basePart₂ x))) z ξ =
        ReciprocityTheory.AnForm.levi (fun w => Real.log (A.h w)) (basePart₂ z) (basePart₂ ξ) := by
      have h := ReciprocityTheory.AnForm.levi_comp (φ := fun w => Real.log (A.h w))
        (τ := ⇑(LiftGraphMetric.oldCLM (ι := ι) r)) (z := z) ξ
        ((LiftGraphMetric.oldCLM (ι := ι) r).analyticAt z) hAlog
      rw [ContinuousLinearMap.fderiv] at h
      exact h
    have hev : (fun x : (Σ k, addIdx ι r k) → ℂ => Real.log (S (basePart₂ x) * A.h (basePart₂ x) ^ 2)) =ᶠ[𝓝 z]
        fun x => Real.log (S (basePart₂ x)) + (2 : ℝ) * Real.log (A.h (basePart₂ x)) := by
      filter_upwards [hUo.mem_nhds hz.1] with x hx'
      have hw' : basePart₂ x ∈ U0 := fun k => hx' (some k)
      rw [Real.log_mul (hSp _ hw').ne' (pow_pos (A.pos _ hw') 2).ne', Real.log_pow]
      norm_num
    have hgraph := hSl z hz ξ hξ
    have hsplit : (fun z' : (Σ k, addIdx ι r k) → ℂ =>
        Real.log (∑ j, ‖z' ⟨none, j⟩‖ ^ 2) / 2 - Real.log (S (basePart₂ z')) / 2) =
        fun z' => (1 / 2 : ℝ) * Real.log (∑ j, ‖z' ⟨none, j⟩‖ ^ 2) +
          (-1 / 2 : ℝ) * Real.log (S (basePart₂ z')) := by
      funext z'
      ring
    show ReciprocityTheory.AnForm.levi _ z ξ = ReciprocityTheory.AnForm.levi _ z ξ
    change ReciprocityTheory.AnForm.levi _ z ξ = (1 : ℕ) * ReciprocityTheory.AnForm.levi _ (basePart₂ z) (basePart₂ ξ) at hgraph
    rw [hsplit, ReciprocityTheory.AnForm.levi_add_smul (f := fun x : (Σ k, addIdx ι r k) → ℂ =>
        (1 / 2 : ℝ) * Real.log (∑ j, ‖x ⟨none, j⟩‖ ^ 2)) (-1 / 2 : ℝ) (contDiffAt_const.mul hL1) hL2 ξ,
      ] at hgraph
    have hhalf := LiftGraphMetric.levi_const_mul (1 / 2 : ℝ) hL1 ξ
    erw [hhalf] at hgraph
    rw [← hcomp] at hgraph
    rw [ReciprocityTheory.AnForm.levi_congr hev, ReciprocityTheory.AnForm.levi_add_smul (2 : ℝ) hL2 hL3 ξ]
    push_cast at hgraph
    linarith

end

end GroundTheory.Heights₂.Heights.Targets
