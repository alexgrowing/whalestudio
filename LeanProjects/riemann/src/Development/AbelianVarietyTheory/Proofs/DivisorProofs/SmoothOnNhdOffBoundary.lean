import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AnalyticLogResolution
open MeasureTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.IndefiniteRowSideFullHecke.BoundaryPolynomialFunctions GlobalTheory.LogResInt
open scoped ENNReal

namespace GlobalTheory.PoincSmooth

open scoped ContDiff

theorem continuousOn_of_holoOn {d : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas d X)
    {U : Set X} {g : X → ℂ} (hg : A.HoloOn U g) : ContinuousOn g U := by
  intro y hy
  obtain ⟨j, hj⟩ := A.cover y
  have h1 : ContinuousAt (g ∘ (A.chart j).symm) (A.chart j y) := by
    refine (hg j (A.chart j y) ⟨(A.chart j).map_source hj, ?_⟩).continuousAt
    simp [(A.chart j).left_inv hj, hy]
  have h2 : ContinuousAt ((g ∘ (A.chart j).symm) ∘ (A.chart j)) y :=
    h1.comp ((A.chart j).continuousAt hj)
  refine (h2.congr ?_).continuousWithinAt
  filter_upwards [(A.chart j).eventually_left_inverse hj] with z hz
  simp [Function.comp, hz]

theorem smoothOn_nhd_off_boundary : ∀ (d : ℕ) (X : Type) [TopologicalSpace X] (A : FinHolAtlas d X) (m : ℕ)
    (α : LocPot X) (Λ : Fin m → LocPot X) (σ : Fin m → X → X → ℂ) (c : ℝ), IsPotential A α →
    (∀ i, IsPotential A (Λ i) ∧ IsSection A (Λ i) (σ i)) → (∀ i y, normSec (Λ i) (σ i) y ≤ 1) →
    ∀ x, x ∉ boundary σ → ∃ O : Set X, IsOpen O ∧ x ∈ O ∧ O ⊆ (poincarePot α Λ σ c).U x ∧
      A.SmoothOn O ((poincarePot α Λ σ c).φ x) := by
  intro d X _ A m α Λ σ c hα hΛ hn x hx
  have hx' : ∀ i, σ i x x ≠ 0 := fun i h => hx ⟨i, h⟩
  set O : Set X := α.U x ∩ ⋂ i, ((Λ i).U x ∩ σ i x ⁻¹' {0}ᶜ) with hOdef
  have hO : IsOpen O := by
    refine (α.isOpen_U x).inter (isOpen_iInter_of_finite fun i => ?_)
    exact (continuousOn_of_holoOn A ((hΛ i).2.1 x)).isOpen_inter_preimage ((Λ i).isOpen_U x)
      isOpen_compl_singleton
  have hxO : x ∈ O := ⟨α.mem_U x, Set.mem_iInter.2 fun i => ⟨(Λ i).mem_U x, hx' i⟩⟩
  refine ⟨O, hO, hxO, fun y hy => ⟨hy.1, Set.mem_univ _⟩, fun j => ?_⟩
  set s := (A.chart j).symm with hs
  set T := (A.chart j).target ∩ s ⁻¹' O with hT
  have hU : ∀ w ∈ T, ∀ i, s w ∈ (Λ i).U x := fun w hw i => (Set.mem_iInter.1 hw.2.2 i).1
  have hnz : ∀ w ∈ T, ∀ i, σ i x (s w) ≠ 0 := fun w hw i => (Set.mem_iInter.1 hw.2.2 i).2
  have hσs : ∀ i, ContDiffOn ℝ ∞ (σ i x ∘ s) T := fun i =>
    ((((hΛ i).2.1 x j).contDiffOn (n := ∞)
      ((A.chart j).isOpen_inter_preimage_symm ((Λ i).isOpen_U x)).uniqueDiffOn).restrict_scalars ℝ).mono
      (fun w hw => ⟨hw.1, hU w hw i⟩)
  have hφ : ∀ i, ContDiffOn ℝ ∞ ((Λ i).φ x ∘ s) T := fun i =>
    ((hΛ i).1.1 x j).mono (fun w hw => ⟨hw.1, hU w hw i⟩)
  have hαs : ContDiffOn ℝ ∞ (α.φ x ∘ s) T := (hα.1 x j).mono (fun w hw => ⟨hw.1, hw.2.1⟩)
  let v : Fin m → (Fin d → ℂ) → ℝ := fun i w => ‖σ i x (s w)‖ * Real.exp (-(Λ i).φ x (s w))
  have hv : ∀ i, ContDiffOn ℝ ∞ (v i) T := fun i =>
    (ContDiffOn.norm ℝ (hσs i) (fun w hw => hnz w hw i)).mul (hφ i).neg.exp
  have hglue : ∀ w ∈ T, ∀ i, normSec (Λ i) (σ i) (s w) = v i w := fun w hw i =>
    (hΛ i).2.2 (s w) x (s w) ⟨(Λ i).mem_U _, hU w hw i⟩
  have hvpos : ∀ w ∈ T, ∀ i, 0 < v i w := fun w hw i =>
    mul_pos (norm_pos_iff.2 (hnz w hw i)) (Real.exp_pos _)
  have hlogv : ∀ i, ContDiffOn ℝ ∞ (fun w => Real.log (v i w)) T := fun i =>
    (hv i).log (fun w hw => (hvpos w hw i).ne')
  have hrpos : ∀ w ∈ T, ∀ i, 0 < Real.exp 1 - 2 * Real.log (v i w) := by
    intro w hw i
    have h1 : Real.log (v i w) ≤ 0 :=
      Real.log_nonpos (hvpos w hw i).le (hglue w hw i ▸ hn i (s w))
    have h2 := Real.exp_pos 1
    linarith
  have hr : ∀ i, ContDiffOn ℝ ∞ (fun w => Real.log (Real.exp 1 - 2 * Real.log (v i w))) T :=
    fun i => (contDiffOn_const.sub (contDiffOn_const.mul (hlogv i))).log
      (fun w hw => (hrpos w hw i).ne')
  have hsum : ContDiffOn ℝ ∞
      (fun w => ∑ i ∈ Finset.univ, Real.log (Real.exp 1 - 2 * Real.log (v i w))) T :=
    ContDiffOn.sum fun i _ => hr i
  have hg : ContDiffOn ℝ ∞ (fun w => α.φ x (s w) +
      -c * (∑ i ∈ Finset.univ, Real.log (Real.exp 1 - 2 * Real.log (v i w))) / 2) T :=
    hαs.add ((contDiffOn_const.mul hsum).div_const 2)
  refine hg.congr fun w hw => ?_
  show α.φ x (s w) + pFun Λ σ c (s w) / 2 = _
  simp only [pFun, rFun]
  congr 3
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 3
  exact congrArg Real.log (hglue w hw i)

end GlobalTheory.PoincSmooth
