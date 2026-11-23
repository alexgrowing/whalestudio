import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DensConst
import Development.AbelianVarietyTheory.Definitions.Divisors.ContinuousBcPt
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalSectionDivisorPullbackGeneric
import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLineFubiniStudyFacts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedChernFormDensityPullbackMatchingCharts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClosedNullSetCharts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsConjFsBasisOfUnitary
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix
open scoped ENNReal

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.MixIso

theorem map_chartMeas {A B : Type} [TopologicalSpace A] [MeasurableSpace A] [BorelSpace A]
    [TopologicalSpace B] [MeasurableSpace B] [BorelSpace B] {n : ℕ} (Φ : A ≃ᵐ B)
    (e' : OpenPartialHomeomorph A (ReciprocityTheory.L2DbarEstimates.V n)) (e : OpenPartialHomeomorph B (ReciprocityTheory.L2DbarEstimates.V n))
    (ρ' : A → ℝ≥0∞) (ρ : B → ℝ≥0∞) (ht : e'.target = e.target)
    (hs : ∀ v ∈ e.target, Φ (e'.symm v) = e.symm v) (hρ : ∀ v ∈ e.target, ρ' (e'.symm v) = ρ (e.symm v)) :
    Measure.map Φ (chartMeas e' ρ') = chartMeas e ρ := by
  unfold chartMeas
  have hae : AEMeasurable e'.symm ((volume.restrict e'.target).withDensity (ρ' ∘ e'.symm)) :=
    (e'.continuousOn_symm.aemeasurable e'.open_target.measurableSet).mono_ac
      (withDensity_absolutelyContinuous _ _)
  rw [AEMeasurable.map_map_of_aemeasurable Φ.measurable.aemeasurable hae, ht]
  have h1 : (volume.restrict e.target).withDensity (ρ' ∘ e'.symm) =
      (volume.restrict e.target).withDensity (ρ ∘ e.symm) :=
    withDensity_congr_ae ((ae_restrict_iff' e.open_target.measurableSet).2
      (Eventually.of_forall fun v hv => hρ v hv))
  rw [h1]
  exact Measure.map_congr ((withDensity_absolutelyContinuous _ _).ae_le
    ((ae_restrict_iff' e.open_target.measurableSet).2 (Eventually.of_forall fun v hv => hs v hv)))

theorem le_map_symm_iff {A B : Type} [MeasurableSpace A] [MeasurableSpace B] (Φ : A ≃ᵐ B)
    (μ : Measure A) (ν : Measure B) : μ ≤ Measure.map Φ.symm ν ↔ Measure.map Φ μ ≤ ν := by
  constructor
  · intro h
    simpa only [MeasurableEquiv.map_map_symm] using Measure.map_mono h Φ.measurable
  · intro h
    simpa only [MeasurableEquiv.map_symm_map] using Measure.map_mono h Φ.symm.measurable

end GlobalTheory.MixIso

namespace GlobalTheory.MixIso

variable {k : Type} [CommRing k] {X Y : Scheme.{0}} {p : X ⟶ Sp k} {q : Y ⟶ Sp k}

theorem inv_comp (π : Y ⟶ X) [IsIso π] (hπ : π ≫ p = q) : inv π ≫ q = p := by
  rw [IsIso.inv_comp_eq, hπ]

def ptH (π : Y ⟶ X) [IsIso π] (hπ : π ≫ p = q) (σ : k →+* ℂ) : CxPts q σ ≃ₜ CxPts p σ where
  toFun := ptMap π hπ σ
  invFun := ptMap (inv π) (inv_comp π hπ) σ
  left_inv y := Subtype.ext (by simp)
  right_inv y := Subtype.ext (by simp)
  continuous_toFun := CxPts.continuous_of_comp (f := π) fun _ => rfl
  continuous_invFun := CxPts.continuous_of_comp (f := inv π) fun _ => rfl

variable {σ : k →+* ℂ} {D : ℕ}

def pullChart (π : Y ⟶ X) [IsIso π] (hπ : π ≫ p = q) (c : AlgChart p σ D) : AlgChart q σ D where
  e := (ptH π hπ σ).transOpenPartialHomeomorph c.e
  U := π ⁻¹ᵁ c.U
  affine := c.affine.preimage_of_isIso π
  x a := π.app c.U (c.x a)
  etale := GlobalTheory.Mean4O.CoverExc.etale_app π hπ c.etale
    (RingHom.Etale.of_bijective (ConcreteCategory.bijective_of_isIso (π.app c.U)))
  source_subset y hy := (mem_ptsIn_preimage (m := ptMap π hπ σ) (fun _ => rfl)).2 (c.source_subset hy)
  apply_eq y hy a := (c.apply_eq _ hy a).trans (ev_of_comp (m := ptMap π hπ σ) (fun _ => rfl) _ _ _)
  holo W f := by
    refine ((c.holo (inv π ⁻¹ᵁ W) ((inv π).app W f)).mono fun v hv => ⟨hv.1,
      (mem_ptsIn_preimage (m := ptMap (inv π) (inv_comp π hπ) σ) (f := inv π) (fun _ => rfl)).2 hv.2⟩).congr
      fun v _ => ?_
    exact ev_of_comp (m := ptMap (inv π) (inv_comp π hπ) σ) (f := inv π) (fun _ => rfl) W f _

theorem pullChart_symm (π : Y ⟶ X) [IsIso π] (hπ : π ≫ p = q) (c : AlgChart p σ D) (v : ReciprocityTheory.L2DbarEstimates.V D) :
    (pullChart π hπ c).e.symm v = ptMap (inv π) (inv_comp π hπ) σ (c.e.symm v) := rfl

end GlobalTheory.MixIso

namespace GlobalTheory.MixIso

variable {k : Type} [CommRing k] {X Y : Scheme.{0}} {p : X ⟶ Sp k} {q : Y ⟶ Sp k} {σ : k →+* ℂ} {D : ℕ}

theorem map_chartMeas_dens (π : Y ⟶ X) [IsIso π] (hπ : π ≫ p = q) (L : Fin D → MLine p σ) (ε : ℤˣ)
    (c : AlgChart p σ D) (c' : AlgChart q σ D) (ht : c'.e.target = c.e.target)
    (hs : ∀ v, ptMap π hπ σ (c'.e.symm v) = c.e.symm v) :
    Measure.map (ptH π hπ σ).toMeasurableEquiv
      (chartMeas c'.e fun y => ENNReal.ofReal ((ε : ℤ) * dens (fun i => (L i).pull π hπ) c' y)) =
      chartMeas c.e fun y => ENNReal.ofReal ((ε : ℤ) * dens L c y) := by
  refine map_chartMeas _ _ _ _ _ ht (fun v _ => hs v) fun v hv => ?_
  rw [← hs v, GlobalTheory.MixPull.dens_pull k X Y p q σ D π hπ L c c' (fun w hw => ?_) _ (c'.e.map_target (ht ▸ hv))]
  have hw' : c'.e w ∈ c.e.target := ht ▸ c'.e.map_source hw
  have e : ptMap π hπ σ w = c.e.symm (c'.e w) := by rw [← hs, c'.e.left_inv hw]
  rw [e]
  exact ⟨c.e.map_target hw', (c.e.right_inv hw').symm⟩

theorem map_part (π : Y ⟶ X) [IsIso π] (hπ : π ≫ p = q) (L : Fin D → MLine p σ) (ε : ℤˣ) :
    Measure.map (ptH π hπ σ).toMeasurableEquiv (part (fun i => (L i).pull π hπ) ε) = part L ε := by
  unfold part glueMeas
  refine le_antisymm ((le_map_symm_iff _ _ _).1 (iSup_le fun c' => (le_map_symm_iff _ _ _).2 ?_))
    (iSup_le fun c => ?_)
  · rw [map_chartMeas_dens π hπ L ε (pullChart (inv π) (inv_comp π hπ) c') c' rfl fun v =>
      Subtype.ext (by simp [pullChart_symm])]
    exact le_iSup (fun c : AlgChart p σ D => chartMeas c.e fun y => ENNReal.ofReal ((ε : ℤ) * dens L c y)) _
  · rw [← map_chartMeas_dens π hπ L ε c (pullChart π hπ c) rfl fun v => (ptH π hπ σ).right_inv _]
    exact Measure.map_mono (le_iSup (fun c' : AlgChart q σ D => chartMeas c'.e fun y =>
      ENNReal.ofReal ((ε : ℤ) * dens (fun i => (L i).pull π hπ) c' y)) _) (MeasurableEquiv.measurable _)

theorem intg_int_pull : ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (σ : k →+* ℂ), IsProjOver p → ∀ (π : Y ⟶ X) [IsIso π] (hπ : π ≫ p = q) (D : ℕ) (L : Fin D → MLine p σ) (f : CxPts p σ → ℝ), (Intg (fun i => (L i).pull π hπ) (fun y => f (ptMap π hπ σ y)) ↔ Intg L f) ∧ Mix.int (fun i => (L i).pull π hπ) (fun y => f (ptMap π hπ σ y)) = Mix.int L f := by
  intro k _ X Y p q σ _ π _ hπ D L f
  simp only [Intg, Mix.int, ← map_part π hπ L, integrable_map_equiv, integral_map_equiv]
  exact ⟨Iff.rfl, rfl⟩

end GlobalTheory.MixIso
