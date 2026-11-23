import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Regularisation.StBoundedChartsOfRegCharts
import GroundTheory.HeightsAndTheta.Heights.Regularisation.ToPotentialChartsChartFun
import GroundTheory.HeightsAndTheta.Heights.Regularisation.ProjLineChartsNotSubsetBall
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular

open Metric Set
open ReciprocityTheory.AnForm.A (IsPsh)
open ReciprocityTheory.AnForm.M (FinHolAtlas IsCompatChart)

noncomputable section

theorem isPsh_comp_smul {D : ℕ} {U : Set (Fin D → ℂ)} {u : (Fin D → ℂ) → ℝ} (h : IsPsh U u) (c : ℂ) :
    IsPsh ((c • ·) ⁻¹' U) (fun z => u (c • z)) := by
  refine ⟨h.1.comp (continuous_const_smul c).continuousOn fun _ hz => hz, fun z w hz => ?_⟩
  have hline : ∀ ζ : ℂ, c • z + ζ • (c • w) = c • (z + ζ • w) := fun ζ => by
    rw [smul_add, smul_comm ζ c w]
  have h2 := h.2 (c • z) (c • w) fun ζ hζ => by rw [hline]; exact hz ζ hζ
  simp only [hline] at h2
  exact h2

def scaleHom (D : ℕ) {c : ℝ} (hc : 0 < c) : (Fin D → ℂ) ≃ₜ (Fin D → ℂ) :=
  Homeomorph.smulOfNeZero (c : ℂ) (by exact_mod_cast hc.ne')

theorem scaleHom_apply (D : ℕ) {c : ℝ} (hc : 0 < c) (z : Fin D → ℂ) :
    scaleHom D hc z = (c : ℂ) • z := rfl

theorem scaleHom_preimage_ball (D : ℕ) {c : ℝ} (hc : 0 < c) :
    scaleHom D hc ⁻¹' ball 0 c ⊆ ball 0 1 := by
  intro z hz
  have hz' : ‖(c : ℂ) • z‖ < c := by simpa [scaleHom_apply] using hz
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc] at hz'
  simpa using (mul_lt_iff_lt_one_right hc).1 hz'

theorem isCompatChart_scale {D : ℕ} {X : Type*} [TopologicalSpace X] {A : FinHolAtlas D X}
    {ψ : OpenPartialHomeomorph X (Fin D → ℂ)} (hψ : IsCompatChart A ψ) {c : ℝ} (hc : 0 < c) :
    IsCompatChart A (ψ.transHomeomorph (scaleHom D hc).symm) := by
  intro j
  have hlin : ∀ a : ℂ, AnalyticOnNhd ℂ (fun z : Fin D → ℂ => a • z) univ :=
    fun a => (a • ContinuousLinearMap.id ℂ (Fin D → ℂ)).analyticOnNhd univ
  refine ⟨(hlin ((c : ℂ)⁻¹)).comp (hψ j).1 (mapsTo_univ _ _), ?_⟩
  have h2 : AnalyticOnNhd ℂ ((A.chart j ∘ ψ.symm) ∘ fun z : Fin D → ℂ => (c : ℂ) • z)
      ((ψ.transHomeomorph (scaleHom D hc).symm).target ∩
        (ψ.transHomeomorph (scaleHom D hc).symm).symm ⁻¹' (A.chart j).source) :=
    (hψ j).2.comp ((hlin (c : ℂ)).mono (subset_univ _)) fun z hz => hz
  exact h2

namespace RegCharts

variable {D : ℕ} {X : Type*} [TopologicalSpace X] {A : FinHolAtlas D X}

def scaled (R : RegCharts A) (M : Fin R.n → ℝ) (hM0 : ∀ j, 0 < M j)
    (hM : ∀ j, closure (R.W' j) ⊆ ball 0 (M j)) : RegCharts A where
  n := R.n
  ψ j := (R.ψ j).transHomeomorph (scaleHom D (hM0 j)).symm
  compat j := isCompatChart_scale (R.compat j) (hM0 j)
  W j := scaleHom D (hM0 j) ⁻¹' (R.W j ∩ ball 0 (M j))
  W' j := scaleHom D (hM0 j) ⁻¹' R.W' j
  W'' j := scaleHom D (hM0 j) ⁻¹' R.W'' j
  isOpen_kappaOpenNeighbourhood j := ((R.isOpen_kappaOpenNeighbourhood j).inter isOpen_ball).preimage (scaleHom D (hM0 j)).continuous
  isOpen_alt j := (R.isOpen_alt j).preimage (scaleHom D (hM0 j)).continuous
  isOpen_alt_alt j := (R.isOpen_alt_alt j).preimage (scaleHom D (hM0 j)).continuous
  W_subset j := fun _ hz => R.W_subset j hz.1
  isCompact_closure_middle j := by
    rw [← (scaleHom D (hM0 j)).preimage_closure]
    exact (scaleHom D (hM0 j)).isCompact_preimage.2 (R.isCompact_closure_middle j)
  closure_W'_subset j := by
    rw [← (scaleHom D (hM0 j)).preimage_closure]
    exact preimage_mono (subset_inter (R.closure_W'_subset j) (hM j))
  closure_W''_subset j := by
    rw [← (scaleHom D (hM0 j)).preimage_closure]
    exact preimage_mono (R.closure_W''_subset j)
  cover x := by
    obtain ⟨j, hx, hxW⟩ := R.cover x
    refine ⟨j, hx, ?_⟩
    show scaleHom D (hM0 j) ((scaleHom D (hM0 j)).symm (R.ψ j x)) ∈ R.W'' j
    rwa [Homeomorph.apply_symm_apply]
  θ := R.θ
  θ_pot := R.θ_pot
  om := R.om
  om_pot := R.om_pot
  om_pos := R.om_pos
  q j z := R.q j (scaleHom D (hM0 j) z)
  q_smooth j := (R.q_smooth j).comp (contDiff_const_smul ((M j : ℂ))).contDiffOn
    fun _ hz => hz.1
  q_θ j y hy hyW := by
    have key : ∀ x, scaleHom D (hM0 j) ((scaleHom D (hM0 j)).symm (R.ψ j x)) = R.ψ j x :=
      fun x => Homeomorph.apply_symm_apply _ _
    have hyW' : R.ψ j y ∈ R.W j := by
      have h : scaleHom D (hM0 j) ((scaleHom D (hM0 j)).symm (R.ψ j y)) ∈ R.W j ∩ ball 0 (M j) := hyW
      rw [key] at h
      exact h.1
    obtain ⟨V, hV, hyV, G, hG, hq⟩ := R.q_θ j y hy hyW'
    refine ⟨V, hV, hyV, G, hG, fun x hx hxW => ?_⟩
    have hxW' : scaleHom D (hM0 j) ((scaleHom D (hM0 j)).symm (R.ψ j x)) ∈ R.W j ∩ ball 0 (M j) := hxW
    rw [key] at hxW'
    have e := hq x hx hxW'.1
    show R.θ.φ y x - R.q j (scaleHom D (hM0 j) ((scaleHom D (hM0 j)).symm (R.ψ j x))) = (G x).re
    rw [key]
    exact e

variable (R : RegCharts A) (M : Fin R.n → ℝ) (hM0 : ∀ j, 0 < M j)
  (hM : ∀ j, closure (R.W' j) ⊆ ball 0 (M j))

theorem scaled_θ : (R.scaled M hM0 hM).θ = R.θ := rfl

theorem scaled_W_subset (j : Fin R.n) : (R.scaled M hM0 hM).W j ⊆ ball 0 1 :=
  (preimage_mono inter_subset_right).trans (scaleHom_preimage_ball D (hM0 j))

end RegCharts

namespace BoundedThPsh

variable {D : ℕ} {X : Type*} [TopologicalSpace X] {A : FinHolAtlas D X} {R : RegCharts A}

def scaled (P : BoundedThPsh R) (M : Fin R.n → ℝ) (hM0 : ∀ j, 0 < M j)
    (hM : ∀ j, closure (R.W' j) ⊆ ball 0 (M j)) : BoundedThPsh (R.scaled M hM0 hM) where
  φ := P.φ
  bdd := P.bdd
  psh j := isPsh_comp_smul
    (GroundTheory.Heights₂.Heights.Regular.isPsh_mono (P.psh j) inter_subset_left) (M j : ℂ)

end BoundedThPsh

theorem BoundedChartsOfRegCharts.proof : BoundedChartsOfRegCharts.Statement := by
  intro X _ _ _ D A R P
  have hb : ∀ j, ∃ M : ℝ, 0 < M ∧ closure (R.W' j) ⊆ ball 0 M := fun j =>
    (R.isCompact_closure_middle j).isBounded.subset_ball_lt 0 0
  choose M hM0 hM using hb
  exact ⟨(P.scaled M hM0 hM).toBoundedPsh (R.scaled_W_subset M hM0 hM), rfl, rfl⟩

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular
