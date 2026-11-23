import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsHaarOnIffGroupsUnitaryUnipotent
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OrbitalIntegralAeConvergenceContinuity
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ConjugationContinuousOnInvertible
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CompactGroupHaarExists
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OppositeWeylSubgroupClosed
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ConjugationInvarianceEverySetting
import Formalism.FormalDegreeBessel.FinalG
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.SParamMeas

open Formalism.QuantumDeterminants

variable {k r : ℕ}

noncomputable def conjInvM (a : B.Mat k r) (x : Mt k r) : Mt k r := a⁻¹ * Matrix.of x * a

theorem meas_mul {α : Type*} [MeasurableSpace α] {f g : α → Mt k r} (hf : Measurable f) (hg : Measurable g) :
    Measurable (fun x => Formalism.FourierDecayAlt.P.B7.mulM (f x) (g x)) :=
  Formalism.FourierDecayAlt.P.B7.continuous_mulM.measurable.comp (hf.prodMk hg)

theorem meas_inv {α : Type*} [MeasurableSpace α] {f : α → Mt k r} (hf : Measurable f) :
    Measurable (fun x => Formalism.FourierDecayAlt.P.B7.invM (f x)) :=
  Formalism.FourierDecayAlt.P.B7.measurable_invM.comp hf

theorem mp_lmul {U : Set (B.Mat k r)} {μ : Measure (Mt k r)} (h : B.IsHaarOn U μ) {a : B.Mat k r} (ha : a ∈ U) :
    MeasurePreserving (lmulM a) μ μ :=
  ⟨meas_mul (f := fun _ => a) measurable_const measurable_id, h.left a ha⟩

theorem mp_rmul {U : Set (B.Mat k r)} {μ : Measure (Mt k r)} (h : B.IsHaarOn U μ) {a : B.Mat k r} (ha : a ∈ U) :
    MeasurePreserving (B.rmulF a) μ μ :=
  ⟨meas_mul (g := fun _ => a) measurable_id measurable_const, h.right a ha⟩

theorem mp_inv {U : Set (B.Mat k r)} {μ : Measure (Mt k r)} (hU : B2.IsClosedSubgroup U) (h : B.IsHaarOn U μ) :
    MeasurePreserving (B2.invM (k := k) (r := r)) μ μ :=
  ⟨Formalism.FourierDecayAlt.P.B7.measurable_invM, Formalism.FourierDecayAlt.P.haar_measure_inversion k r U μ hU h⟩

theorem mp_conj {z : Fin (2 * r + k + 1) → ℂ} {μ : Measure (Mt k r)} (hz : inWb k r z) (hT : 0 < Tz k r z)
    (h : B.IsHaarOn (Nset k r) μ) {a : B.Mat k r} (ha : a ∈ UWset k r z) :
    MeasurePreserving (conjM a) μ μ :=
  ⟨meas_mul (g := fun _ => (a⁻¹ : B.Mat k r)) (meas_mul (f := fun _ => a) measurable_const measurable_id)
    measurable_const, Formalism.FourierDecayAlt.P.b2_conjInvRaw_proof k r z μ hz hT h a ha⟩

theorem mp_conj_inv {z : Fin (2 * r + k + 1) → ℂ} {μ : Measure (Mt k r)} (hz : inWb k r z) (hT : 0 < Tz k r z)
    (h : B.IsHaarOn (Nset k r) μ) {a : B.Mat k r} (ha : a ∈ UWset k r z) :
    MeasurePreserving (conjInvM a) μ μ := by
  have hW := Formalism.FourierDecayAlt.P.weyl_subgroup_closed k r z
  have := mp_conj hz hT h (hW.inv_mem a ha)
  have e : conjM (a⁻¹) = conjInvM a := by
    funext x
    unfold conjM conjInvM
    rw [Matrix.nonsing_inv_nonsing_inv _ (hW.unit a ha)]
  rwa [e] at this

end GlobalTheory.SParamMeas

open GlobalTheory.SParamMeas in

theorem GlobalTheory.sParam_measurePreserving : ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (μW μN : Measure (Formalism.QuantumDeterminants.Mt k r)), 1 ≤ k → Formalism.QuantumDeterminants.inWb k r z → 0 < Formalism.QuantumDeterminants.Tz k r z → PI.BesselPeriodGGP.IsHaarOn (Formalism.QuantumDeterminants.UWset k r z) μW → PI.BesselPeriodGGP.IsHaarOn (Formalism.QuantumDeterminants.Nset k r) μN → (∀ h₀ ∈ Formalism.QuantumDeterminants.UWset k r z, ∀ n₀ ∈ Formalism.QuantumDeterminants.Nset k r, MeasurePreserving (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r => (((fun i j => (Matrix.of p.1 * h₀ : Mx k r) i j), (fun i j => (h₀⁻¹ * Matrix.of p.2 * h₀ * n₀ : Mx k r) i j)) : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r)) (μW.prod μN) (μW.prod μN) ∧ MeasurePreserving (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r => (((fun i j => (h₀ * Matrix.of p.1 : Mx k r) i j), (fun i j => ((Matrix.of p.1)⁻¹ * n₀ * Matrix.of p.1 * Matrix.of p.2 : Mx k r) i j)) : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r)) (μW.prod μN) (μW.prod μN)) ∧ MeasurePreserving (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r => (((fun i j => ((Matrix.of p.1)⁻¹ : Mx k r) i j), (fun i j => (Matrix.of p.1 * (Matrix.of p.2)⁻¹ * (Matrix.of p.1)⁻¹ : Mx k r) i j)) : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r)) (μW.prod μN) (μW.prod μN) ∧ MeasurePreserving (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r => (((fun i j => (Matrix.of p.1 : Mx k r) i j), (fun i j => (Matrix.of p.1 * Matrix.of p.2 * (Matrix.of p.1)⁻¹ : Mx k r) i j)) : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r)) (μW.prod μN) (μW.prod μN) ∧ MeasurePreserving (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r => (((fun i j => (Matrix.of p.1 : Mx k r) i j), (fun i j => ((Matrix.of p.1)⁻¹ * Matrix.of p.2 * Matrix.of p.1 : Mx k r) i j)) : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r)) (μW.prod μN) (μW.prod μN) ∧ MeasurePreserving (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r => (((fun i j => ((Matrix.of p.1)⁻¹ : Mx k r) i j), (fun i j => ((Matrix.of p.2)⁻¹ : Mx k r) i j)) : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r)) (μW.prod μN) (μW.prod μN) ∧ ∀ᵐ p ∂(μW.prod μN), Matrix.of p.1 ∈ Formalism.QuantumDeterminants.UWset k r z ∧ Matrix.of p.2 ∈ Formalism.QuantumDeterminants.Nset k r := by
  intro k r z μW μN hk hz hT hW0 hN0
  have hW : B.IsHaarOn (Formalism.QuantumDeterminants.UWset k r z) μW := ((GlobalTheory.HaarNotions.isHaarOn_iff_groups k r μW).2.2 z hz hT hk).1 hW0
  have hN : B.IsHaarOn (Formalism.QuantumDeterminants.Nset k r) μN := (GlobalTheory.HaarNotions.isHaarOn_iff_groups k r μN).2.1.1 hN0
  have := hW0.1
  have := hN0.1
  have cW := Formalism.FourierDecayAlt.P.weyl_subgroup_closed k r z
  have cN := Formalism.FourierDecayAlt.P.unipotent_radical_closed k r
  have aW := Formalism.FourierDecayAlt.P.B7.ae_mem hW
  have aN := Formalism.FourierDecayAlt.P.B7.ae_mem hN
  have m1 : Measurable (Prod.fst : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r → _) := measurable_fst
  have m2 : Measurable (Prod.snd : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r → _) := measurable_snd
  refine ⟨fun h₀ hh n₀ hn => ⟨?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
  · exact (mp_rmul hW hh).prod ((mp_rmul hN hn).comp (mp_conj_inv hz hT hN hh))
  · have m3 : Measurable (fun _ : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r => (Matrix.of.symm n₀ : Formalism.QuantumDeterminants.Mt k r)) :=
      measurable_const
    refine (mp_lmul hW hh).skew_product
      (g := fun (a x : Formalism.QuantumDeterminants.Mt k r) => Formalism.QuantumDeterminants.lmulM ((Matrix.of a)⁻¹ * n₀ * Matrix.of a) x)
      (meas_mul (meas_mul (meas_mul (meas_inv m1) m3) m1) m2) ?_
    filter_upwards [aW] with a ha
    refine hN.left _ ?_
    have := (Formalism.QuantumDeterminants.unitary_weyl_normal_holds k r z hz _ (cW.inv_mem _ ha) n₀ hn).1
    rwa [Matrix.nonsing_inv_nonsing_inv _ (cW.unit _ ha)] at this
  · refine (mp_inv cW hW).skew_product
      (g := fun (a x : Formalism.QuantumDeterminants.Mt k r) => Formalism.QuantumDeterminants.conjM (Matrix.of a) (B2.invM x))
      (meas_mul (meas_mul m1 (meas_inv m2)) (meas_inv m1)) ?_
    filter_upwards [aW] with a ha
    exact ((mp_conj hz hT hN ha).comp (mp_inv cN hN)).map_eq
  · refine (MeasurePreserving.id μW).skew_product
      (g := fun (a x : Formalism.QuantumDeterminants.Mt k r) => Formalism.QuantumDeterminants.conjM (Matrix.of a) x)
      (meas_mul (meas_mul m1 m2) (meas_inv m1)) ?_
    filter_upwards [aW] with a ha
    exact (mp_conj hz hT hN ha).map_eq
  · refine (MeasurePreserving.id μW).skew_product
      (g := fun (a x : Formalism.QuantumDeterminants.Mt k r) =>
        conjInvM (Matrix.of a) x)
      (meas_mul (meas_mul (meas_inv m1) m2) m1) ?_
    filter_upwards [aW] with a ha
    exact (mp_conj_inv hz hT hN ha).map_eq
  · exact (mp_inv cW hW).prod (mp_inv cN hN)
  · exact (Measure.quasiMeasurePreserving_fst.ae aW).and (Measure.quasiMeasurePreserving_snd.ae aN)
