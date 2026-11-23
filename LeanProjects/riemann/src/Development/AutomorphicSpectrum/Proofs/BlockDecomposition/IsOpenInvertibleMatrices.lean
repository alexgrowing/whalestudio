import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.WaveSt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsMultOfFintype

noncomputable section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace Convolution
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC
open GlobalTheory.CompanionTheory.WaveMult
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.WaveMult.AvgJoint

theorem isOpen_invertible_matrices (n : ℕ) : IsOpen (GLs n) := by
  have hc : Continuous (fun y : Mat n => y.det) := Continuous.matrix_det continuous_id
  exact isOpen_ne.preimage hc

theorem avg_joint_smooth : ∀ (n : ℕ) {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
    (U : ℝ → Mat n → V) (g : ℝ → ℝ) (T : ℝ), ContDiffOn ℝ ∞ (Function.uncurry U) (Set.univ ×ˢ GLs n) →
    IsBump g T → ContDiffOn ℝ ∞ (Function.uncurry fun t x => ∫ s, (g s : ℂ) • U (t + s) x) (Set.univ ×ˢ GLs n) := by
  intro n V _ _ _ U g T hU hg
  obtain ⟨hgs, hev, hsupp⟩ := hg
  set S : Set (ℝ × Mat n) := Set.univ ×ˢ GLs n with hS
  have hSo : IsOpen S := isOpen_univ.prod (isOpen_invertible_matrices n)
  let h : ℝ × Mat n → ℝ → V := fun p y => ((g (-y) : ℝ) : ℂ) • U (p.1 - y) p.2
  have hh : ContDiffOn ℝ ∞ (Function.uncurry h) (S ×ˢ Set.univ) := by
    have h1 : ContDiff ℝ ∞ (fun q : (ℝ × Mat n) × ℝ => ((g (-q.2) : ℝ) : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp (hgs.comp contDiff_snd.neg)
    have h2 : ContDiff ℝ ∞ (fun q : (ℝ × Mat n) × ℝ => (q.1.1 - q.2, q.1.2)) :=
      ((contDiff_fst.comp contDiff_fst).sub contDiff_snd).prodMk (contDiff_snd.comp contDiff_fst)
    have h3 : ContDiffOn ℝ ∞ (fun q : (ℝ × Mat n) × ℝ => Function.uncurry U (q.1.1 - q.2, q.1.2)) (S ×ˢ Set.univ) := by
      refine hU.comp h2.contDiffOn ?_
      rintro ⟨⟨t, x⟩, y⟩ ⟨hp, -⟩
      exact ⟨Set.mem_univ _, hp.2⟩
    exact h1.contDiffOn.smul h3
  have hk : IsCompact (Metric.closedBall (0 : ℝ) |T|) := isCompact_closedBall 0 |T|
  have hz : ∀ p, ∀ x, p ∈ S → x ∉ Metric.closedBall (0 : ℝ) |T| → h p x = 0 := by
    intro p x _ hx
    have hx' : |T| < |x| := by simpa [Metric.mem_closedBall, Real.dist_eq] using hx
    have : g (-x) = 0 := hsupp _ (by rw [abs_neg]; exact lt_of_le_of_lt (le_abs_self T) hx')
    simp [h, this]
  have hloc : LocallyIntegrable (fun _ : ℝ => (1 : ℝ)) (volume : Measure ℝ) :=
    (continuous_const).locallyIntegrable
  have hc := contDiffOn_convolution_right_with_param (𝕜 := ℝ) (μ := (volume : Measure ℝ)) (n := ⊤)
    (f := fun _ : ℝ => (1 : ℝ)) (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] V →L[ℝ] V) hSo hk hz hloc hh
  have hcomp : ContDiffOn ℝ ∞ (fun p : ℝ × Mat n => ((fun _ : ℝ => (1 : ℝ)) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] h p) 0) S := by
    refine hc.comp (contDiff_id.prodMk contDiff_const).contDiffOn ?_
    intro p hp
    exact ⟨hp, Set.mem_univ _⟩
  refine hcomp.congr ?_
  rintro ⟨t, x⟩ -
  simp [convolution_def, h, Function.uncurry]

end GlobalTheory.CompanionTheory.WaveMult.AvgJoint
