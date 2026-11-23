import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointIsotropicDecomposition
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open scoped ENNReal

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.UnfoldRat

def ratEquiv (D : D7) (m n : ℕ) : Matrix (Fin m) (Fin n) D.host.E ≃ GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.ratMx D m n :=
  Equiv.ofBijective (fun ξ => ⟨ξ.map (incA D), ξ, rfl⟩)
    ⟨fun _ _ h => GlobalTheory.MixModel.rat_injective (congrArg Subtype.val h), fun ⟨_, ξ, hξ⟩ => ⟨ξ, Subtype.ext hξ⟩⟩

theorem countable_ratMx (D : D7) (m n : ℕ) : Countable (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.ratMx D m n) := by
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := GlobalTheory.MixModel.lattice_Mx D m n
  haveI : DiscreteTopology (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.ratMx D m n) := i5
  exact TopologicalSpace.separableSpace_iff_countable.1 inferInstance

theorem countable_mat (D : D7) (m n : ℕ) : Countable (Matrix (Fin m) (Fin n) D.host.E) := by
  haveI := countable_ratMx D m n
  exact (ratEquiv D m n).injective.countable

theorem lintegral_unfold {D : D7} {m n : ℕ} {μ : Measure (Mx D m n)} {𝓨 : Set (Mx D m n)}
    (hcov : IsCovolOne (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.ratMx D m n) μ 𝓨) (φ : Mx D m n → ℝ≥0∞) :
    ∫⁻ u, φ u ∂μ = ∑' ξ : Matrix (Fin m) (Fin n) D.host.E, ∫⁻ t in 𝓨, φ (ξ.map (incA D) + t) ∂μ := by
  obtain ⟨i1, i2, i3, i4, -⟩ := GlobalTheory.MixModel.lattice_Mx D m n
  haveI : BorelSpace (Mx D m n) := ⟨rfl⟩
  haveI := countable_ratMx D m n
  haveI := hcov.1
  rw [hcov.2.1.lintegral_eq_tsum'' φ, ← (ratEquiv D m n).tsum_eq]
  rfl

theorem integral_unfold {D : D7} {m n : ℕ} {μ : Measure (Mx D m n)} {𝓨 : Set (Mx D m n)}
    (hcov : IsCovolOne (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.ratMx D m n) μ 𝓨) (φ : Mx D m n → ℂ) (hφ : Integrable φ μ) :
    ∫ u, φ u ∂μ = ∑' ξ : Matrix (Fin m) (Fin n) D.host.E, ∫ t in 𝓨, φ (ξ.map (incA D) + t) ∂μ := by
  obtain ⟨i1, i2, i3, i4, -⟩ := GlobalTheory.MixModel.lattice_Mx D m n
  haveI : BorelSpace (Mx D m n) := ⟨rfl⟩
  haveI := countable_ratMx D m n
  haveI := hcov.1
  rw [hcov.2.1.integral_eq_tsum'' φ hφ, ← (ratEquiv D m n).tsum_eq]
  rfl

theorem unfold : ∀ (D : D7) (m n : ℕ) (X : Type) [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [SecondCountableTopology X] (ν : Measure X) [IsFiniteMeasure ν] (μ : Measure (Mx D m n)) (𝓨 : Set (Mx D m n)),
    IsCovolOne (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.ratMx D m n) μ 𝓨 → ∀ (h : X → Mx D m n → ℂ), Continuous (Function.uncurry h) →
    ∀ M : ℝ, (∀ x u, Summable (fun ξ : Matrix (Fin m) (Fin n) D.host.E => ‖h x (ξ.map (incA D) + u)‖) ∧
      ∑' ξ : Matrix (Fin m) (Fin n) D.host.E, ‖h x (ξ.map (incA D) + u)‖ ≤ M) →
    Integrable (fun u => ∫ x, h x u ∂ν) μ ∧ ∫ u, (∫ x, h x u ∂ν) ∂μ =
      ∫ t in 𝓨, (∫ x, ∑' ξ : Matrix (Fin m) (Fin n) D.host.E, h x (ξ.map (incA D) + t) ∂ν) ∂μ := by
  intro D m n X _ _ _ _ ν _ μ 𝓨 hcov h hc M hM
  obtain ⟨i1, i2, i3, i4, -⟩ := GlobalTheory.MixModel.lattice_Mx D m n
  haveI : BorelSpace (Mx D m n) := ⟨rfl⟩
  haveI := countable_mat D m n
  haveI := hcov.1
  haveI : FirstCountableTopology (Mx D m n) := @TopologicalSpace.SecondCountableTopology.to_firstCountableTopology _ _ i3
  have hr0 : (0 : Matrix (Fin m) (Fin n) D.host.E).map (incA D) = 0 := Matrix.map_zero _ (map_zero (incA D))

  have hb : ∀ x u, ‖h x u‖ ≤ M := fun x u => by
    have h0 := (hM x u).1.le_tsum 0 (fun _ _ => norm_nonneg _)
    rw [hr0, zero_add] at h0
    exact h0.trans (hM x u).2
  have hcx : ∀ x, Continuous (h x) := fun x => hc.comp (continuous_const.prodMk continuous_id)
  have hcu : ∀ u, Continuous fun x => h x u := fun u => hc.comp (continuous_id.prodMk continuous_const)
  have hmeas : Measurable (Function.uncurry h) := hc.measurable

  have hmx : ∀ x (ξ : Matrix (Fin m) (Fin n) D.host.E), Measurable fun t => ‖h x (ξ.map (incA D) + t)‖ₑ :=
    fun x ξ => ((hcx x).comp (continuous_add_left _)).measurable.enorm
  have hmu : ∀ t (ξ : Matrix (Fin m) (Fin n) D.host.E), Measurable fun x => ‖h x (ξ.map (incA D) + t)‖ₑ :=
    fun t ξ => (hcu (ξ.map (incA D) + t)).measurable.enorm
  have hsum : ∀ x t, ∑' ξ : Matrix (Fin m) (Fin n) D.host.E, ‖h x (ξ.map (incA D) + t)‖ₑ ≤ ENNReal.ofReal M := fun x t => by
    simp_rw [← ofReal_norm_eq_enorm]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => norm_nonneg _) (hM x t).1]
    exact ENNReal.ofReal_le_ofReal (hM x t).2
  have hlx : ∀ x, ∫⁻ u, ‖h x u‖ₑ ∂μ ≤ ENNReal.ofReal M := fun x => by
    have e1 : ∫⁻ t in 𝓨, ∑' ξ : Matrix (Fin m) (Fin n) D.host.E, ‖h x (ξ.map (incA D) + t)‖ₑ ∂μ =
        ∑' ξ : Matrix (Fin m) (Fin n) D.host.E, ∫⁻ t in 𝓨, ‖h x (ξ.map (incA D) + t)‖ₑ ∂μ :=
      lintegral_tsum fun ξ => (hmx x ξ).aemeasurable
    rw [lintegral_unfold hcov (fun u => ‖h x u‖ₑ), ← e1]
    refine (lintegral_mono fun t => hsum x t).trans ?_
    rw [setLIntegral_const, hcov.2.2, mul_one]

  have hGc : Continuous fun u => ∫ x, h x u ∂ν :=
    continuous_of_dominated (bound := fun _ => M) (fun u => (hcu u).aestronglyMeasurable)
      (fun u => Filter.Eventually.of_forall fun x => hb x u) (integrable_const M)
      (Filter.Eventually.of_forall fun x => hcx x)

  have hGi : Integrable (fun u => ∫ x, h x u ∂ν) μ := by
    refine ⟨hGc.aestronglyMeasurable, ?_⟩
    have h1 : ∫⁻ u, ‖∫ x, h x u ∂ν‖ₑ ∂μ ≤ ∫⁻ u, ∫⁻ x, ‖h x u‖ₑ ∂ν ∂μ :=
      lintegral_mono fun u => enorm_integral_le_lintegral_enorm _
    have h2 : ∫⁻ u, ∫⁻ x, ‖h x u‖ₑ ∂ν ∂μ = ∫⁻ x, ∫⁻ u, ‖h x u‖ₑ ∂μ ∂ν :=
      lintegral_lintegral_swap (hmeas.enorm.comp measurable_swap).aemeasurable
    have h3 : ∫⁻ x, ∫⁻ u, ‖h x u‖ₑ ∂μ ∂ν ≤ ENNReal.ofReal M * ν Set.univ := by
      rw [← lintegral_const]; exact lintegral_mono fun x => hlx x
    exact lt_of_le_of_lt (h1.trans (h2.le.trans h3)) (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _))
  refine ⟨hGi, ?_⟩
  rw [integral_unfold hcov _ hGi]

  have hA : ∑' ξ : Matrix (Fin m) (Fin n) D.host.E, ∫⁻ t in 𝓨, ‖∫ x, h x (ξ.map (incA D) + t) ∂ν‖ₑ ∂μ ≠ ∞ := by
    rw [← lintegral_unfold hcov (fun u => ‖∫ x, h x u ∂ν‖ₑ)]; exact hGi.2.ne
  have e3 : ∫ t in 𝓨, ∑' ξ : Matrix (Fin m) (Fin n) D.host.E, ∫ x, h x (ξ.map (incA D) + t) ∂ν ∂μ =
      ∑' ξ : Matrix (Fin m) (Fin n) D.host.E, ∫ t in 𝓨, ∫ x, h x (ξ.map (incA D) + t) ∂ν ∂μ :=
    integral_tsum (fun ξ => (hGc.comp (continuous_add_left (ξ.map (incA D)))).aestronglyMeasurable) hA
  rw [← e3]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)

  have hB : ∑' ξ : Matrix (Fin m) (Fin n) D.host.E, ∫⁻ x, ‖h x (ξ.map (incA D) + t)‖ₑ ∂ν ≠ ∞ := by
    have e2 : ∫⁻ x, ∑' ξ : Matrix (Fin m) (Fin n) D.host.E, ‖h x (ξ.map (incA D) + t)‖ₑ ∂ν =
        ∑' ξ : Matrix (Fin m) (Fin n) D.host.E, ∫⁻ x, ‖h x (ξ.map (incA D) + t)‖ₑ ∂ν :=
      lintegral_tsum fun ξ => (hmu t ξ).aemeasurable
    rw [← e2]
    refine ne_of_lt (lt_of_le_of_lt (lintegral_mono fun x => hsum x t) ?_)
    rw [lintegral_const]; exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)
  have e4 : ∫ x, ∑' ξ : Matrix (Fin m) (Fin n) D.host.E, h x (ξ.map (incA D) + t) ∂ν =
      ∑' ξ : Matrix (Fin m) (Fin n) D.host.E, ∫ x, h x (ξ.map (incA D) + t) ∂ν :=
    integral_tsum (fun (ξ : Matrix (Fin m) (Fin n) D.host.E) => (hcu (ξ.map (incA D) + t)).aestronglyMeasurable) hB
  exact e4.symm

end GlobalTheory.UnfoldRat
