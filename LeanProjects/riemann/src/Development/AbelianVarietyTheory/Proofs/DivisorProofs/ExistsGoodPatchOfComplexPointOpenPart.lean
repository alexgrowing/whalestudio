import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EndValuedForm11Coeffs
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedFrameEventuallyNearComplexPointStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramMatrixSmoothIsUnitInHolomorphicChartStatement

set_option autoImplicit false

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

namespace GlobalTheory.GoodTop

theorem exists_goodPatch_of_mem : ∀ {F : Type} [Field F] {σ : F →+* ℂ} {X : Var F} {m : ℕ} (E : Fr (ratOf X) (fun _ : Unit => m) 0) (O : X.X.Opens) (H : Mat (fun _ : Unit => m) X.Fn → CxPts X.str σ → Mat (fun _ : Unit => m) ℂ), IsMetricOn E O H → ∀ y ∈ ptsIn X.str σ O, ∃ e S A W c, y ∈ W ∧ GoodPatch E O H e S A W c := by
  intro F _ σ X m E O H hH y hy
  classical
  obtain ⟨ch, hc⟩ := AlgChart.exists_mem_source (D := X.dim) (p := X.str) (σ := σ) y
  obtain ⟨A, hA⟩ := E.nonempty (under y)
  have hhol : IsHoloChart ch.e := ch.holo
  obtain ⟨hsm, hu⟩ := GlobalTheory.T.gramMatrix_smooth_isUnit_in_holomorphicChart E O H hH hhol hy hc hA
  set G : V X.dim → Matrix (Fin m) (Fin m) ℂ := fun v => H A (ch.e.symm v) () with hG
  have h1 : ((0 : WithTop ℕ∞) + 1) ≤ ∞ := by exact_mod_cast le_top
  have h2 : ((0 : WithTop ℕ∞) + 2) ≤ ∞ := by
    rw [zero_add]
    first
    | exact (WithTop.coe_le_coe (a := (2 : ℕ∞)) (b := ⊤)).2 le_top
    | exact ENat.LEInfty.out
    | simp
    | decide
  have hconn : ∀ (a : Fin X.dim) (i j : Fin m),
      ContinuousAt (fun z => conn G (ch.e z) (coordVec a) i j) y := fun a i j =>
    ((hsm.conn hu h1 (coordVec a)) i j).continuousAt.comp (ch.e.continuousAt hc)
  have hcurv : ∀ (a b : Fin X.dim) (i j : Fin m),
      ContinuousAt (fun z => curv G (ch.e z) (coordVec a) (coordVec b) i j) y := fun a b i j =>
    ((hsm.curv hu h2 (coordVec a) (coordVec b)) i j).continuousAt.comp (ch.e.continuousAt hc)
  let C : ℝ := (∑ a : Fin X.dim, ∑ i : Fin m, ∑ j : Fin m, (‖conn G (ch.e y) (coordVec a) i j‖ + 1)) +
    ∑ a : Fin X.dim, ∑ b : Fin X.dim, ∑ i : Fin m, ∑ j : Fin m,
      (‖curv G (ch.e y) (coordVec a) (coordVec b) i j‖ + 1)
  have hP1 : ∀ a i j, ‖conn G (ch.e y) (coordVec a) i j‖ + 1 ≤ C := by
    intro a i j
    refine le_add_of_le_of_nonneg ?_ (by positivity)
    refine (Finset.single_le_sum (f := fun j => ‖conn G (ch.e y) (coordVec a) i j‖ + 1)
      (fun _ _ => by positivity) (Finset.mem_univ j)).trans ?_
    refine (Finset.single_le_sum (f := fun i => ∑ j : Fin m, (‖conn G (ch.e y) (coordVec a) i j‖ + 1))
      (fun _ _ => by positivity) (Finset.mem_univ i)).trans ?_
    exact Finset.single_le_sum (f := fun a => ∑ i : Fin m, ∑ j : Fin m, (‖conn G (ch.e y) (coordVec a) i j‖ + 1))
      (fun _ _ => by positivity) (Finset.mem_univ a)
  have hP2 : ∀ a b i j, ‖curv G (ch.e y) (coordVec a) (coordVec b) i j‖ + 1 ≤ C := by
    intro a b i j
    refine le_add_of_nonneg_of_le (by positivity) ?_
    refine (Finset.single_le_sum (f := fun j => ‖curv G (ch.e y) (coordVec a) (coordVec b) i j‖ + 1)
      (fun _ _ => by positivity) (Finset.mem_univ j)).trans ?_
    refine (Finset.single_le_sum (f := fun i => ∑ j : Fin m, (‖curv G (ch.e y) (coordVec a) (coordVec b) i j‖ + 1))
      (fun _ _ => by positivity) (Finset.mem_univ i)).trans ?_
    refine (Finset.single_le_sum (f := fun b => ∑ i : Fin m, ∑ j : Fin m, (‖curv G (ch.e y) (coordVec a) (coordVec b) i j‖ + 1))
      (fun _ _ => by positivity) (Finset.mem_univ b)).trans ?_
    exact Finset.single_le_sum (f := fun a => ∑ b : Fin X.dim, ∑ i : Fin m, ∑ j : Fin m, (‖curv G (ch.e y) (coordVec a) (coordVec b) i j‖ + 1))
      (fun _ _ => by positivity) (Finset.mem_univ a)
  let T : Set (CxPts X.str σ) := {z | z ∈ ch.e.source ∧ z ∈ ptsIn X.str σ O ∧ A ∈ E.S (under z) ∧
    (∀ a i j, ‖conn G (ch.e z) (coordVec a) i j‖ ≤ C) ∧
    (∀ a b i j, ‖curv G (ch.e z) (coordVec a) (coordVec b) i j‖ ≤ C)}
  have hT : T ∈ 𝓝 y := by
    have e1 : ∀ᶠ z in 𝓝 y, ∀ a i j, ‖conn G (ch.e z) (coordVec a) i j‖ ≤ C := by
      simp only [eventually_all]
      intro a i j
      filter_upwards [(hconn a i j).norm.eventually (gt_mem_nhds (lt_add_one _))] with z hz
      exact hz.le.trans ((le_refl _).trans (by linarith [hP1 a i j]))
    have e2 : ∀ᶠ z in 𝓝 y, ∀ a b i j, ‖curv G (ch.e z) (coordVec a) (coordVec b) i j‖ ≤ C := by
      simp only [eventually_all]
      intro a b i j
      filter_upwards [(hcurv a b i j).norm.eventually (gt_mem_nhds (lt_add_one _))] with z hz
      exact hz.le.trans ((le_refl _).trans (by linarith [hP2 a b i j]))
    filter_upwards [ch.e.open_source.mem_nhds hc, (isOpen_ptsIn (p := X.str) (σ := σ) O).mem_nhds hy,
      GlobalTheory.T.adaptedFrame_eventually_near_complexPoint E hA, e1, e2] with z h₁ h₂ h₃ h₄ h₅
    exact ⟨h₁, h₂, h₃, h₄, h₅⟩
  refine ⟨ch.e, ∅, A, interior T, C, mem_interior_iff_mem_nhds.2 hT, ?_⟩
  have hsub : ∀ z ∈ interior T, z ∈ T := fun z hz => interior_subset hz
  refine ⟨hhol, isOpen_interior, fun z hz => (hsub z hz).1, fun z hz => (hsub z hz).2.2.1,
    fun z _ a ha => absurd ha (Finset.notMem_empty a), fun z hz => ?_, fun z hz _ a i j => ?_,
    fun z hz _ a b i j => ?_⟩
  · simp only [Finset.notMem_empty, false_imp_iff, implies_true, iff_true]
    exact (hsub z hz).2.1
  · simp only [poinWt, Finset.notMem_empty, if_false, mul_one]
    exact (hsub z hz).2.2.2.1 a i j
  · simp only [poinWt, Finset.notMem_empty, if_false, mul_one]
    exact (hsub z hz).2.2.2.2 a b i j

end GlobalTheory.GoodTop
