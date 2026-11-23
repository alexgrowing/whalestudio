import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LocalWeightCharts.StarOfInv
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LocalWeightCharts.NotMidCases

noncomputable section

open MeasureTheory Matrix
open scoped ENNReal NNReal

namespace WlocSk.WRI

open Formalism.QuantumDeterminants WlocSk.HM

variable {k r : ℕ}

theorem haar_right_compact {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G] [LocallyCompactSpace G] [SecondCountableTopology G]
    [T2Space G] [CompactSpace G] (g : G) :
    (Measure.haar : Measure G).map (· * g) = Measure.haar := by
  set μ : Measure G := Measure.haar
  set ν : Measure G := μ.map (· * g)
  have hν : ν = Measure.haarScalarFactor ν μ • μ := Measure.isMulLeftInvariant_eq_smul ν μ
  have hmass : ν Set.univ = μ Set.univ := by
    simp only [ν]
    rw [Measure.map_apply (measurable_mul_const g) MeasurableSet.univ, Set.preimage_univ]
  have h0 : μ Set.univ ≠ 0 := by
    intro h; exact (NeZero.ne μ) (Measure.measure_univ_eq_zero.mp h)
  have htop : μ Set.univ ≠ ∞ := measure_ne_top μ _
  have hc : ((Measure.haarScalarFactor ν μ : ℝ≥0) : ℝ≥0∞) = 1 := by
    have e := hmass
    rw [hν, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at e
    have e2 : ((Measure.haarScalarFactor ν μ : ℝ≥0) : ℝ≥0∞) * μ Set.univ = 1 * μ Set.univ := by
      rw [one_mul]; exact e
    exact (ENNReal.mul_left_inj h0 htop).mp e2
  rw [hν]
  have : Measure.haarScalarFactor ν μ = 1 := by exact_mod_cast hc
  rw [this, one_smul]

theorem hmeas_right (U : Set (Mx k r)) (hU : ClSub U) (hc : IsCompact U) (g : Mx k r) (hg : g ∈ U) :
    (hmeas U hU).map (fun x : Mt k r => fun i j => (Matrix.of x * g) i j) = hmeas U hU := by
  have : CompactSpace (Grp U hU) := isCompact_iff_compactSpace.mp hc
  have hvt : Measurable (Grp.vt : Grp U hU → Mt k r) := (val_cemb U hU).continuous.measurable
  have hR : Measurable (fun x : Mt k r => fun i j => (Matrix.of x * g) i j) := by
    have : Continuous (fun x : Mt k r => fun i j => (Matrix.of x * g) i j) :=
      Continuous.matrix_mul continuous_id continuous_const
    exact this.measurable
  unfold hmeas
  rw [Measure.map_map hR hvt]
  have : (fun x : Mt k r => fun i j => (Matrix.of x * g) i j) ∘ (Grp.vt : Grp U hU → Mt k r) =
      (Grp.vt : Grp U hU → Mt k r) ∘ (fun a => a * Grp.mk g hg) := by
    funext a; rfl
  rw [this, ← Measure.map_map hvt (measurable_mul_const _), haar_right_compact]

end WlocSk.WRI

open WlocSk.HM WlocSk.WRI in
theorem unipotent_right_invariance : WlocSk.WRightInv := by
  intro k r z μW hz hT hH _ h hh
  obtain ⟨c, -, -, hμ⟩ := haar_unique _ (uw_clsub z) μW hH
  rw [hμ, Measure.map_smul, hmeas_right _ _ (compactW z hz hT) h hh]
