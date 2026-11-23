import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SecondCountableTopologyOfIsProjOver

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.Points GlobalTheory.TopForm GlobalTheory.ChartGlue GlobalTheory.CechPic
open scoped ContDiff Manifold

namespace GlobalTheory

open CxPts

variable {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {σ : k →+* ℂ} {D : ℕ}

namespace AnRead

variable (R : AnRead p σ D)

@[reducible] def chartedSpace : ChartedSpace (V D) (CxPts p σ) where
  atlas := range fun i => (R.chart i).e
  chartAt y := (R.chart (R.cover y).choose).e
  mem_chart_source y := (R.cover y).choose_spec
  chart_mem_atlas _ := mem_range_self _

theorem isManifold : letI := R.chartedSpace; IsManifold 𝓘(ℝ, V D) ∞ (CxPts p σ) := by
  let := R.chartedSpace
  refine isManifold_of_contDiffOn _ _ _ ?_
  rintro _ _ ⟨i, rfl⟩ ⟨j, rfl⟩
  have ho := isOpen_over (R.chart i).e (R.chart j).e.open_source
  have ht : ContDiffOn ℝ ∞ ((R.chart j).e ∘ (R.chart i).e.symm) _ := (contDiffOn_piLp 2).2 fun a =>
    contDiffOn_real ho (differentiableOn_euclidean.1 ((R.chart i).holo_trans _) a)
  simpa using ht

variable {R}

theorem smoothOn_iff_contMDiffOn {S : Set (CxPts p σ)} (hS : IsOpen S) {f : CxPts p σ → ℝ} :
    letI := R.chartedSpace; R.SmoothOn S f ↔ ContMDiffOn 𝓘(ℝ, V D) 𝓘(ℝ) ∞ f S := by
  let := R.chartedSpace
  have := R.isManifold
  constructor
  · intro h
    rw [contMDiffOn_iff]
    refine ⟨h.continuousOn hS, fun x w => ?_⟩
    simp only [mfld_simps, chartAt_self_eq]
    exact h (R.cover x).choose
  · intro h i
    have hi : (R.chart i).e ∈ IsManifold.maximalAtlas 𝓘(ℝ, V D) ∞ (CxPts p σ) :=
      IsManifold.subset_maximalAtlas (mem_range_self i)
    exact contMDiffOn_iff_contDiffOn.1 (h.comp
      ((contMDiffOn_symm_of_mem_maximalAtlas hi).mono inter_subset_left) fun _ hv => hv.2)

end AnRead

namespace Weight

theorem exists_smooth_weight_of_t2 [T2Space (CxPts p σ)] [SecondCountableTopology (CxPts p σ)]
    (R : AnRead p σ D) (B : LB Y) (hB : B.IsLB) : ∃ φ : Weight p σ B, φ.IsSmooth R := by
  let := R.chartedSpace
  have := R.isManifold
  have : LocallyCompactSpace (CxPts p σ) := ChartedSpace.locallyCompactSpace (V D) _
  obtain ⟨χ, hχ⟩ := SmoothPartitionOfUnity.exists_isSubordinate 𝓘(ℝ, V D) isClosed_univ
    (fun i => ptsIn p σ (B.U i)) (fun _ => isOpen_ptsIn _)
    fun y _ => mem_iUnion.2 ⟨_, mem_pick hB y⟩
  refine ⟨⟨hB, fun i y => ∑ᶠ l, χ l y • Real.log (‖gv p σ B i l y‖ ^ 2), fun i j y hi hj => ?_⟩,
    fun i => ?_⟩
  · rw [← χ.sum_finsupport_smul_eq_finsum y fun l y => Real.log (‖gv p σ B j l y‖ ^ 2),
      ← χ.sum_finsupport_smul_eq_finsum y fun l y => Real.log (‖gv p σ B i l y‖ ^ 2),
      ← one_smul ℝ (Real.log (‖gv p σ B i j y‖ ^ 2)), ← χ.sum_finsupport y (mem_univ y),
      Finset.sum_smul, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun l hl => ?_
    have hl' : y ∈ ptsIn p σ (B.U l) := hχ l (subset_tsupport _ ((χ.mem_finsupport y).1 hl))
    rw [← gv_mul hB hi hj hl', log_normSq_mul (gv_ne_zero hi hj) (gv_ne_zero hj hl'), ← smul_sub,
      add_sub_cancel_left]
  · refine (AnRead.smoothOn_iff_contMDiffOn (isOpen_ptsIn _)).2 fun y hy => ?_
    refine (χ.contMDiffAt_finsum (n := (⊤ : ℕ∞))
      (g := fun l y => Real.log (‖gv p σ B i l y‖ ^ 2)) fun l hl => ?_).contMDiffWithinAt
    have ho := isOpen_ptsIn (p := p) (σ := σ) (B.U i ⊓ B.U l)
    exact ((AnRead.smoothOn_iff_contMDiffOn ho).1 ((R.holoOn_ev _ (B.g i l).val).smoothOn_log ho
      fun _ hz => ev_ne_zero hz (B.g i l).isUnit)).contMDiffAt
      (ho.mem_nhds (mem_ptsIn_inf.2 ⟨hy, hχ l hl⟩))

theorem exists_isSmooth_of_isProjOver (h : IsProjOver p) (R : AnRead p σ D) (B : LB Y)
    (hB : B.IsLB) : ∃ φ : Weight p σ B, φ.IsSmooth R :=
  have := t2Space_cxPts_of_isProjOver σ h
  have := secondCountableTopology_of_isProjOver σ h
  exists_smooth_weight_of_t2 R B hB

end Weight

namespace WeightFamily

variable [SmoothOfRelativeDimension D p] {κ : Type}

def ofWeights [T2Space (CxPts p σ)] [SecondCountableTopology (CxPts p σ)] (R : AnRead p σ D)
    (K : CanonLB p D) (L : κ → LB Y) (φ : ∀ a, Weight p σ (L a)) (h : ∀ a, (φ a).IsSmooth R) :
    WeightFamily R κ where
  K := K
  φK := (Weight.exists_smooth_weight_of_t2 R K.bundle K.isLB).choose
  smoothK := (Weight.exists_smooth_weight_of_t2 R K.bundle K.isLB).choose_spec
  L := L
  φ := φ
  smooth := h

end WeightFamily

end GlobalTheory
