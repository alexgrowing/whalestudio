import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

namespace GlobalTheory.HSAmp.VolDens

theorem meas_integral_in_chart : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ),
    IsArithVar p D → ∀ (σ : k →+* ℂ) (ω : VolDens p σ D) (c : AlgChart p σ D) (S : Set (CxPts p σ))
    (F : CxPts p σ → ℝ), MeasurableSet S → S ⊆ c.e.source → Continuous F →
    ω.meas S = ∫⁻ v in c.e '' S, ENNReal.ofReal (ω.dens c (c.e.symm v)) ∧
    ∫ y in S, F y ∂ω.meas = ∫ v in c.e '' S, F (c.e.symm v) * ω.dens c (c.e.symm v) := by
  intro k _ X _ p D hX σ ω c S F hS hc hF
  haveI : SecondCountableTopology (CxPts p σ) :=
    CxPts.secondCountableTopology_of_isProjOver σ hX.isProjOver
  have hmeas : ∀ A : Set (CxPts p σ), MeasurableSet A → A ⊆ c.e.source →
      ω.meas A = ∫⁻ v in c.e '' A, ENNReal.ofReal (ω.dens c (c.e.symm v)) := by
    intro A hA hAc
    rw [VolDens.meas, ChartGlue.glueMeas_apply _ _ (fun c c' => c.holo_trans c') (fun c c' y hy hy' => by
      rw [ω.trans c c' y hy hy', ENNReal.ofReal_mul (sq_nonneg _)]) c hA hAc,
      ChartGlue.chartMeas_apply_of_subset _ _ hA hAc]
  refine ⟨hmeas S hS hc, ?_⟩
  have hSm : MeasurableSet (c.e '' S) := ChartGlue.measurableSet_image c.e hS hc
  have hSt : c.e '' S ⊆ c.e.target := by
    rintro _ ⟨y, hy, rfl⟩
    exact c.e.map_source (hc hy)
  set f : _ → ENNReal := fun v => ENNReal.ofReal (ω.dens c (c.e.symm v)) with hf
  set ν := (volume.restrict (c.e '' S)).withDensity f with hν
  have haem : AEMeasurable c.e.symm ν :=
    ((c.e.continuousOn_symm.mono hSt).aemeasurable hSm).mono_ac (withDensity_absolutelyContinuous _ _)
  have hrest : ω.meas.restrict S = Measure.map c.e.symm ν := by
    ext A hA
    rw [Measure.restrict_apply hA, Measure.map_apply_of_aemeasurable haem hA,
      hmeas (A ∩ S) (hA.inter hS) (Set.inter_subset_right.trans hc), hν, withDensity_apply' _ _,
      Measure.restrict_restrict' hSm]
    congr 2
    ext v
    constructor
    · rintro ⟨y, ⟨hyA, hyS⟩, rfl⟩
      exact ⟨by simpa [c.e.left_inv (hc hyS)] using hyA, ⟨y, hyS, rfl⟩⟩
    · rintro ⟨hvA, y, hyS, rfl⟩
      exact ⟨y, ⟨by simpa [c.e.left_inv (hc hyS)] using hvA, hyS⟩, rfl⟩
  have hfm : AEMeasurable f (volume.restrict (c.e '' S)) := by
    refine (ENNReal.measurable_ofReal.comp_aemeasurable ?_)
    refine ContinuousOn.aemeasurable ?_ hSm
    refine (ω.cont c).comp (c.e.continuousOn_symm.mono hSt) ?_
    intro v hv
    exact c.e.map_target (hSt hv)
  rw [hrest, integral_map haem hF.aestronglyMeasurable, hν,
    integral_withDensity_eq_integral_toReal_smul₀ hfm (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  refine setIntegral_congr_fun hSm fun v hv => ?_
  have hpos := ω.pos c _ (c.e.map_target (hSt hv))
  simp only [hf, smul_eq_mul, ENNReal.toReal_ofReal hpos.le, mul_comm]

end GlobalTheory.HSAmp.VolDens
