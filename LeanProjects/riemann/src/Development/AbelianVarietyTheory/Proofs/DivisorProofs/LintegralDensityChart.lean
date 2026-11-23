import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalEqCurve

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.ArInt
open scoped ENNReal

namespace GlobalTheory.MixDens

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ} {D : ℕ}

theorem IsDens.part_restrict_eq_map [SecondCountableTopology (CxPts p σ)] {ρ : AlgChart p σ D → CxPts p σ → ℝ}
    (hρ : IsDens ρ) (c : AlgChart p σ D) {T : Set (CxPts p σ)} (hT : MeasurableSet T) (hc : T ⊆ c.e.source) :
    (part ρ).restrict T = Measure.map c.e.symm
      ((volume.restrict (c.e '' T)).withDensity fun v => ENNReal.ofReal (ρ c (c.e.symm v))) := by
  have hI : MeasurableSet (c.e '' T) := ChartGlue.measurableSet_image _ hT hc
  have hsub : c.e '' T ⊆ c.e.target := by
    rintro _ ⟨y, hy, rfl⟩
    exact c.e.map_source (hc hy)
  have hs : AEMeasurable c.e.symm (volume.restrict (c.e '' T)) :=
    (c.e.continuousOn_symm.mono hsub).aemeasurable hI
  refine Measure.ext fun S hS => ?_
  have hST : MeasurableSet (S ∩ T) := hS.inter hT
  have hI' : MeasurableSet (c.e '' (S ∩ T)) := ChartGlue.measurableSet_image _ hST (inter_subset_right.trans hc)
  have hset : c.e.symm ⁻¹' S ∩ c.e '' T = c.e '' (S ∩ T) := by
    ext v
    constructor
    · rintro ⟨h1, y, hy, rfl⟩
      refine ⟨y, ⟨?_, hy⟩, rfl⟩
      simpa only [mem_preimage, c.e.left_inv (hc hy)] using h1
    · rintro ⟨y, ⟨h1, hy⟩, rfl⟩
      refine ⟨?_, y, hy, rfl⟩
      simpa only [mem_preimage, c.e.left_inv (hc hy)] using h1
  rw [Measure.restrict_apply hS, hρ.part_apply c hST (inter_subset_right.trans hc),
    Measure.map_apply_of_aemeasurable (hs.mono_ac (withDensity_absolutelyContinuous _ _)) hS,
    ← restrict_withDensity hI, Measure.restrict_apply' hI, hset, withDensity_apply _ hI']

theorem lintegral_part_chart (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ) (D : ℕ)
    [SecondCountableTopology (CxPts p σ)] (ρ : AlgChart p σ D → CxPts p σ → ℝ) (hρ : IsDens ρ)
    (c : AlgChart p σ D) (T : Set (CxPts p σ)) (hT : MeasurableSet T) (hc : T ⊆ c.e.source)
    (h : CxPts p σ → ℝ≥0∞) (hh : Measurable h) :
    ∫⁻ y in T, h y ∂part ρ = ∫⁻ v in c.e '' T, h (c.e.symm v) * ENNReal.ofReal (ρ c (c.e.symm v)) := by
  have hI : MeasurableSet (c.e '' T) := ChartGlue.measurableSet_image _ hT hc
  have hsub : c.e '' T ⊆ c.e.target := by
    rintro _ ⟨y, hy, rfl⟩
    exact c.e.map_source (hc hy)
  have hs : AEMeasurable c.e.symm (volume.restrict (c.e '' T)) :=
    (c.e.continuousOn_symm.mono hsub).aemeasurable hI
  have hd : AEMeasurable (fun v => ENNReal.ofReal (ρ c (c.e.symm v))) (volume.restrict (c.e '' T)) :=
    (((hρ.2 c).mono hsub).aemeasurable hI).ennreal_ofReal
  rw [hρ.part_restrict_eq_map c hT hc,
    lintegral_map' hh.aemeasurable (hs.mono_ac (withDensity_absolutelyContinuous _ _)),
    lintegral_withDensity_eq_lintegral_mul₀ hd (hh.comp_aemeasurable' hs)]
  exact lintegral_congr fun v => mul_comm _ _

end GlobalTheory.MixDens
