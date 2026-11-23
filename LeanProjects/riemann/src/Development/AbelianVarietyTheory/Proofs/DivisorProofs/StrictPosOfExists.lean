import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SecondCountableTopologyOfIsProjOver
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FlatLocA
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.DerivDerivNonposOfIsLocalMax
import ReciprocityTheory.L2DbarEstimates.LeviForms.OfRealNormSqSumMul
import ReciprocityTheory.L2DbarEstimates.LeviForms.LogNormSq

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open GlobalTheory.Points GlobalTheory.TopForm GlobalTheory.ChartGlue GlobalTheory.CechPic
open scoped ContDiff

namespace GlobalTheory

open CxPts

variable {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {σ : k →+* ℂ} {D : ℕ}

namespace AlgChart

variable (c c' : AlgChart p σ D) {S : Set (CxPts p σ)} {y : CxPts p σ} {f g : CxPts p σ → ℝ}

def levi (f : CxPts p σ → ℝ) (y : CxPts p σ) (ξ : Fin D → ℂ) : ℝ :=
  (leviV D (fun v => (f (c.e.symm v) : ℂ)) (c.e y) ξ).re

def dtrans (y : CxPts p σ) (ξ : Fin D → ℂ) : Fin D → ℂ :=
  fun b => fderiv ℂ (c'.e ∘ c.e.symm) (c.e y) (WithLp.toLp 2 ξ) b

variable {c c'}

theorem levi_congr (hS : IsOpen S) (hy : y ∈ c.e.source) (hyS : y ∈ S) (h : ∀ z ∈ S, f z = g z)
    (ξ : Fin D → ℂ) : c.levi f y ξ = c.levi g y ξ :=
  congrArg Complex.re (leviV_congr (eventually_of_mem
    ((isOpen_over c.e hS).mem_nhds (mem_over c.e hy hyS)) fun _ hv =>
      congrArg Complex.ofReal (h _ hv.2)) ξ)

theorem levi_add (hf : ContDiffAt ℝ 2 (f ∘ c.e.symm) (c.e y))
    (hg : ContDiffAt ℝ 2 (g ∘ c.e.symm) (c.e y)) (ξ : Fin D → ℂ) :
    c.levi (fun z => f z + g z) y ξ = c.levi f y ξ + c.levi g y ξ :=
  (congrArg Complex.re (flA_leviV_add hf hg ξ)).trans (Complex.add_re _ _)

theorem levi_const_mul (a : ℝ) (hf : ContDiffAt ℝ 2 (f ∘ c.e.symm) (c.e y)) (ξ : Fin D → ℂ) :
    c.levi (fun z => a * f z) y ξ = a * c.levi f y ξ :=
  (congrArg Complex.re (LocalMaximumSecondDerivative.leviV_ofReal_const_mul a hf ξ)).trans (Complex.re_ofReal_mul _ _)

theorem levi_log_normSq {u : CxPts p σ → ℂ} (hS : IsOpen S) (hy : y ∈ c.e.source) (hyS : y ∈ S)
    (hu : DifferentiableOn ℂ (u ∘ c.e.symm) (c.e.target ∩ c.e.symm ⁻¹' S)) (h0 : u y ≠ 0)
    (ξ : Fin D → ℂ) : c.levi (fun z => Real.log (‖u z‖ ^ 2)) y ξ = 0 :=
  congrArg Complex.re (flA_leviV_log_normSq (h := u ∘ c.e.symm)
    (eventually_of_mem ((isOpen_over c.e hS).mem_nhds (mem_over c.e hy hyS)) fun _ hv =>
      hu.differentiableAt ((isOpen_over c.e hS).mem_nhds hv))
    (by rwa [Function.comp_apply, c.e.left_inv hy]) ξ)

theorem levi_trans (hy : y ∈ c.e.source) (hy' : y ∈ c'.e.source)
    (hf : ContDiffAt ℝ 2 (f ∘ c'.e.symm) (c'.e y)) (ξ : Fin D → ℂ) :
    c.levi f y ξ = c'.levi f y (c.dtrans c' y ξ) := by
  have ho := isOpen_over c.e c'.e.open_source
  have hn := ho.mem_nhds (mem_over c.e hy hy')
  have ht : ContDiffAt ℂ 2 (c'.e ∘ c.e.symm) (c.e y) :=
    (((contDiffOn_piLp 2).2 fun a => contDiffOn_of_differentiableOn D _ _ ho
      (differentiableOn_euclidean.1 (c.holo_trans c') a)).contDiffAt hn).of_le
      (WithTop.coe_le_coe.2 le_top)
  have e : (c'.e ∘ c.e.symm) (c.e y) = c'.e y := congrArg c'.e (c.e.left_inv hy)
  have hU : ContDiffAt ℝ 2 (fun v => (f (c'.e.symm v) : ℂ)) ((c'.e ∘ c.e.symm) (c.e y)) :=
    e ▸ Complex.ofRealCLM.contDiff.contDiffAt.comp _ hf
  have := flA_leviV_comp hU ht ξ
  rw [e] at this
  refine congrArg Complex.re (Eq.trans (leviV_congr (eventually_of_mem hn fun v hv => ?_) ξ) this)
  simp only [Function.comp_apply, c'.e.left_inv hv.2]

theorem dtrans_ne_zero (hy : y ∈ c.e.source) (hy' : y ∈ c'.e.source) {ξ : Fin D → ℂ}
    (hξ : ξ ≠ 0) : c.dtrans c' y ξ ≠ 0 := fun h => by
  have hd : transDet c.e c'.e y ≠ 0 := rv_chart c c' hy hy' ▸
    rv_ne_zero _ _ (c.source_subset hy) (c'.source_subset hy')
  have hi := (LinearMap.isUnit_iff_ker_eq_bot _).1
    ((LinearMap.isUnit_iff_isUnit_det _).2 hd.isUnit)
  have := LinearMap.ker_eq_bot'.1 hi (WithLp.toLp 2 ξ) (PiLp.ext fun b => congrFun h b)
  exact hξ (congrArg WithLp.ofLp this)

end AlgChart

namespace AnRead

variable {R : AnRead p σ D} {S : Set (CxPts p σ)} {y : CxPts p σ}

theorem SmoothOn.contDiffAt_two {f : CxPts p σ → ℝ} (h : R.SmoothOn S f) (hS : IsOpen S)
    {c : AlgChart p σ D} (hy : y ∈ c.e.source) (hyS : y ∈ S) :
    ContDiffAt ℝ 2 (f ∘ c.e.symm) (c.e y) :=
  ((h.chart hS c).contDiffAt ((isOpen_over c.e hS).mem_nhds (mem_over c.e hy hyS))).of_le
    (WithTop.coe_le_coe.2 le_top)

theorem levi_eq_of_add_log {f g : CxPts p σ → ℝ} {u : CxPts p σ → ℂ} (hS : IsOpen S)
    (hf : R.SmoothOn S f) (hu : R.HoloOn S u) (h0 : ∀ z ∈ S, u z ≠ 0)
    (h : ∀ z ∈ S, g z = f z + Real.log (‖u z‖ ^ 2)) {c : AlgChart p σ D} (hy : y ∈ c.e.source)
    (hyS : y ∈ S) (ξ : Fin D → ℂ) : c.levi g y ξ = c.levi f y ξ := by
  rw [AlgChart.levi_congr hS hy hyS h, AlgChart.levi_add (hf.contDiffAt_two hS hy hyS)
    ((hu.smoothOn_log hS h0).contDiffAt_two hS hy hyS),
    AlgChart.levi_log_normSq hS hy hyS (hu.chart hS c) (h0 y hyS), add_zero]

end AnRead

namespace Weight

open AnRead

variable {R R' : AnRead p σ D} {A B : LB Y} {φ : Weight p σ B} {ψ : Weight p σ A}
  {c : AlgChart p σ D} {y : CxPts p σ}

theorem IsSmooth.contDiffAt_two (h : φ.IsSmooth R) {i : B.ι} (hy : y ∈ c.e.source)
    (hi : y ∈ ptsIn p σ (B.U i)) : ContDiffAt ℝ 2 (φ.φ i ∘ c.e.symm) (c.e y) :=
  (h i).contDiffAt_two (isOpen_ptsIn _) hy hi

theorem IsSmooth.levi_frame (h : φ.IsSmooth R) {i j : B.ι} (hy : y ∈ c.e.source)
    (hi : y ∈ ptsIn p σ (B.U i)) (hj : y ∈ ptsIn p σ (B.U j)) (ξ : Fin D → ℂ) :
    c.levi (φ.φ i) y ξ = c.levi (φ.φ j) y ξ :=
  levi_eq_of_add_log ((isOpen_ptsIn (B.U i)).inter (isOpen_ptsIn (B.U j)))
    ((h j).mono inter_subset_right) (u := gv p σ B i j)
    (holoOn_ev_of_subset _ fun _ => mem_ptsIn_inf.2) (fun _ hz => gv_ne_zero hz.1 hz.2)
    (fun z hz => by rw [φ.trans i j z hz.1 hz.2, sub_add_cancel]) hy ⟨hi, hj⟩ ξ

theorem StrictPos.semiPos (h : φ.StrictPos R) : φ.SemiPos R := fun i c y hy ξ => by
  rcases eq_or_ne ξ 0 with rfl | hξ
  · simp [leviV]
  · exact (h i c y hy ξ hξ).le

theorem SemiPos.chart (h : φ.SemiPos R) (hs : φ.IsSmooth R) {i : B.ι} (hy : y ∈ c.e.source)
    (hi : y ∈ ptsIn p σ (B.U i)) (ξ : Fin D → ℂ) : 0 ≤ c.levi (φ.φ i) y ξ := by
  obtain ⟨j, hj⟩ := R.cover y
  rw [AlgChart.levi_trans hy hj (hs.contDiffAt_two hj hi)]
  exact h i j y ⟨hj, hi⟩ _

theorem StrictPos.chart (h : φ.StrictPos R) (hs : φ.IsSmooth R) {i : B.ι} (hy : y ∈ c.e.source)
    (hi : y ∈ ptsIn p σ (B.U i)) {ξ : Fin D → ℂ} (hξ : ξ ≠ 0) : 0 < c.levi (φ.φ i) y ξ := by
  obtain ⟨j, hj⟩ := R.cover y
  rw [AlgChart.levi_trans hy hj (hs.contDiffAt_two hj hi)]
  exact h i j y ⟨hj, hi⟩ _ (AlgChart.dtrans_ne_zero hy hj hξ)

theorem SemiPos.of_anRead (h : φ.SemiPos R) (hs : φ.IsSmooth R) (R' : AnRead p σ D) :
    φ.SemiPos R' := fun _ _ _ hy ξ => h.chart hs hy.1 hy.2 ξ

theorem StrictPos.of_anRead (h : φ.StrictPos R) (hs : φ.IsSmooth R) (R' : AnRead p σ D) :
    φ.StrictPos R' := fun _ _ _ hy _ hξ => h.chart hs hy.1 hy.2 hξ

theorem IsSmooth.semiPos_of_exists (hs : φ.IsSmooth R)
    (h : ∀ y, ∃ (c : AlgChart p σ D) (i : B.ι), y ∈ c.e.source ∧ y ∈ ptsIn p σ (B.U i) ∧
      ∀ ξ, 0 ≤ c.levi (φ.φ i) y ξ) : φ.SemiPos R := fun j c' y hy ξ => by
  obtain ⟨c, i, hc, hi, h⟩ := h y
  exact (h _).trans_eq ((hs.levi_frame hc hi hy.2 _).trans
    (AlgChart.levi_trans hy.1 hc (hs.contDiffAt_two hc hy.2) ξ).symm)

theorem IsSmooth.strictPos_of_exists (hs : φ.IsSmooth R)
    (h : ∀ y, ∃ (c : AlgChart p σ D) (i : B.ι), y ∈ c.e.source ∧ y ∈ ptsIn p σ (B.U i) ∧
      ∀ ξ, ξ ≠ 0 → 0 < c.levi (φ.φ i) y ξ) : φ.StrictPos R := fun j c' y hy ξ hξ => by
  obtain ⟨c, i, hc, hi, h⟩ := h y
  exact (h _ (AlgChart.dtrans_ne_zero hy.1 hc hξ)).trans_eq ((hs.levi_frame hc hi hy.2 _).trans
    (AlgChart.levi_trans hy.1 hc (hs.contDiffAt_two hc hy.2) ξ).symm)

theorem levi_tens (hψ : ψ.IsSmooth R) (hφ : φ.IsSmooth R) {i : (CechPic.tens A B).ι}
    (hy : y ∈ c.e.source) (hi : y ∈ ptsIn p σ ((CechPic.tens A B).U i)) (ξ : Fin D → ℂ) :
    c.levi ((ψ.tens φ).φ i) y ξ = c.levi (ψ.φ i.1) y ξ + c.levi (φ.φ i.2) y ξ :=
  AlgChart.levi_add (hψ.contDiffAt_two hy (mem_ptsIn_inf.1 hi).1)
    (hφ.contDiffAt_two hy (mem_ptsIn_inf.1 hi).2) ξ

theorem levi_zpow (hφ : φ.IsSmooth R) (n : ℤ) {j : PUnit → B.ι} (hy : y ∈ c.e.source)
    (hj : y ∈ ptsIn p σ (B.U (j PUnit.unit))) (ξ : Fin D → ℂ) :
    c.levi ((φ.zpow n).φ j) y ξ = n * c.levi (φ.φ (j PUnit.unit)) y ξ := by
  rw [funext (φ.zpow_φ n j)]
  exact AlgChart.levi_const_mul _ (hφ.contDiffAt_two hy hj) ξ

theorem levi_ofIso (hφ : φ.IsSmooth R) (hA : A.IsLB) (w : LB.Iso B A) (hw : w.IsGen) {a : A.ι}
    {b : B.ι} (hy : y ∈ c.e.source) (ha : y ∈ ptsIn p σ (A.U a)) (hb : y ∈ ptsIn p σ (B.U b))
    (ξ : Fin D → ℂ) : c.levi ((φ.ofIso hA w hw).φ a) y ξ = c.levi (φ.φ b) y ξ :=
  levi_eq_of_add_log ((isOpen_ptsIn (A.U a)).inter (isOpen_ptsIn (B.U b)))
    ((hφ b).mono inter_subset_right)
    (holoOn_ev_of_subset (w.s (a, b)).val fun _ => mem_ptsIn_inf.2)
    (fun _ hz => ev_iso_ne_zero w hz.2 hz.1) (fun _ hz => ofPairs_φ hz.1 hz.2) hy ⟨ha, hb⟩ ξ

theorem SemiPos.tens (h' : ψ.SemiPos R) (h : φ.SemiPos R) (hψ : ψ.IsSmooth R)
    (hφ : φ.IsSmooth R) : (ψ.tens φ).SemiPos R := fun i c y hy ξ =>
  (add_nonneg (h' _ c y ⟨hy.1, (mem_ptsIn_inf.1 hy.2).1⟩ ξ)
    (h _ c y ⟨hy.1, (mem_ptsIn_inf.1 hy.2).2⟩ ξ)).trans_eq (levi_tens hψ hφ hy.1 hy.2 ξ).symm

theorem SemiPos.zpow (h : φ.SemiPos R) (hφ : φ.IsSmooth R) {n : ℤ} (hn : 0 ≤ n) :
    (φ.zpow n).SemiPos R := fun j c y hy ξ =>
  (mul_nonneg (Int.cast_nonneg hn) (h _ c y ⟨hy.1, mem_pow_iff.1 hy.2⟩ ξ)).trans_eq
    (levi_zpow hφ n hy.1 (mem_pow_iff.1 hy.2) ξ).symm

theorem StrictPos.zpow (h : φ.StrictPos R) (hφ : φ.IsSmooth R) {n : ℤ} (hn : 0 < n) :
    (φ.zpow n).StrictPos R := fun j c y hy ξ hξ =>
  (mul_pos (Int.cast_pos.2 hn) (h _ c y ⟨hy.1, mem_pow_iff.1 hy.2⟩ ξ hξ)).trans_eq
    (levi_zpow hφ n hy.1 (mem_pow_iff.1 hy.2) ξ).symm

theorem SemiPos.pow (h : φ.SemiPos R) (hφ : φ.IsSmooth R) (n : ℕ) : (φ.pow n).SemiPos R :=
  h.zpow hφ (Int.natCast_nonneg n)

theorem StrictPos.pow (h : φ.StrictPos R) (hφ : φ.IsSmooth R) {n : ℕ} (hn : 0 < n) :
    (φ.pow n).StrictPos R := h.zpow hφ (Int.natCast_pos.2 hn)

theorem SemiPos.ofIso (h : φ.SemiPos R) (hφ : φ.IsSmooth R) (hA : A.IsLB) (w : LB.Iso B A)
    (hw : w.IsGen) : (φ.ofIso hA w hw).SemiPos R := fun _ c y hy ξ =>
  (h _ c y ⟨hy.1, mem_pick φ.isLB y⟩ ξ).trans_eq
    (levi_ofIso hφ hA w hw hy.1 hy.2 (mem_pick φ.isLB y) ξ).symm

theorem StrictPos.ofIso (h : φ.StrictPos R) (hφ : φ.IsSmooth R) (hA : A.IsLB) (w : LB.Iso B A)
    (hw : w.IsGen) : (φ.ofIso hA w hw).StrictPos R := fun _ c y hy ξ hξ =>
  (h _ c y ⟨hy.1, mem_pick φ.isLB y⟩ ξ hξ).trans_eq
    (levi_ofIso hφ hA w hw hy.1 hy.2 (mem_pick φ.isLB y) ξ).symm

theorem semiPos_fs {α : Type*} [Fintype α] {e : α → B.ι → CxPts p σ → ℂ} (hB : B.IsLB)
    (he : ∀ a, e a ∈ R.holSec B) (h : NoCommonZero e) :
    (fs hB e (fun a => (he a).1) h).SemiPos R := fun i c y hy ξ => by
  have ho := isOpen_over (R.chart c).e (isOpen_ptsIn (p := p) (σ := σ) (B.U i))
  have hc (a) : ContDiffAt ℂ 2 (e a i ∘ (R.chart c).e.symm) ((R.chart c).e y) :=
    ((contDiffOn_of_differentiableOn D _ _ ho ((he a).2 i c)).contDiffAt
      (ho.mem_nhds (mem_over _ hy.1 hy.2))).of_le (WithTop.coe_le_coe.2 le_top)
  have hs (v) : ∑ j, Complex.normSq ((e ((Fintype.equivFin α).symm j) i ∘ (R.chart c).e.symm) v) =
      ∑ a, ‖e a i ((R.chart c).e.symm v)‖ ^ 2 :=
    Fintype.sum_equiv (Fintype.equivFin α).symm _ _ fun _ => Complex.normSq_eq_norm_sq _
  have := leviV_log_sum_nonneg (fun j => contDiffAt_normSq_comp (hc ((Fintype.equivFin α).symm j)))
    (fun j => logPshAt_normSq (hc _))
    (by rw [hs, (R.chart c).e.left_inv hy.1]; exact h.sum_pos hy.2) ξ
  simp only [hs] at this
  exact this

end Weight

namespace WeightFamily.Reading

variable [SmoothOfRelativeDimension D p] {R : AnRead p σ D} {κ : Type} [Fintype κ] [DecidableEq κ]
  [T2Space (CxPts p σ)] [SecondCountableTopology (CxPts p σ)] {F : WeightFamily R κ} {B : LB Y}
  {m : Option κ → ℤ} {r : F.Reading B m} {φ : Weight p σ B}

theorem Isometric.isSmooth (h : r.Isometric φ) : φ.IsSmooth R := fun i =>
  AnRead.smoothOn_of_cover (fun c => (F.atlas.chart c).open_source)
    (fun y _ => ⟨_, F.atlas.mem_pick y⟩) fun c => by
    have hS := (F.atlas.chart c).open_source.inter (isOpen_ptsIn (p := p) (σ := σ) (B.U i))
    have h₁ : R.SmoothOn (F.atlas.chart c).source (F.atlas.ph m c) := fun j =>
      ContDiffOn.sum (f := fun o v => m o * F.ph₀ o c ((R.chart j).e.symm v)) fun o _ =>
        contDiffOn_const.mul (by
          rcases o with _ | a
          · exact ((F.smoothK c.2.1).mono (fun _ => mem_K) j).add
              ((AnRead.holoOn_ev_of_subset _ fun _ hz =>
                mem_ptsIn_inf.2 ⟨mem_U hz, mem_K hz⟩).smoothOn_log (F.atlas.chart c).open_source
                (fun _ hz => rv_ne_zero _ _ (mem_U hz) (mem_K hz)) j)
          · exact (F.smooth a _).mono (fun _ hz => mem_L hz a) j)
    rw [inter_comm]
    exact AnRead.SmoothOn.congr
      (f := fun z => F.atlas.ph m c z - Real.log (‖r.u c i z‖ ^ 2))
      (fun j => (h₁.mono inter_subset_left j).sub
        ((r.holo c i).smoothOn_log hS (fun z hz => r.ne c i z hz.1 hz.2) j))
      fun z hz => eq_sub_of_add_eq (h c i z hz.1 hz.2).symm

end WeightFamily.Reading

end GlobalTheory
