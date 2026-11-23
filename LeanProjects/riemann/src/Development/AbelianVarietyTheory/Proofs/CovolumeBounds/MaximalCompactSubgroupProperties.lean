import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsKMeas
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CompactGroupHaarExists
import Formalism.FormalDegreeBessel.FormalDegreeRatio.GBasic

open Matrix MeasureTheory Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 GlobalTheory.HCXi
open scoped ENNReal ComplexOrder

noncomputable section

namespace GlobalTheory.HCXi.KGroup

theorem closedSubgroup (k r : ℕ) : IsClosedSubgroup (Kset k r) := by
  have hG := Formalism.FourierDecayAlt.P.unitary_group_closed k r
  refine ⟨⟨hG.one_mem, by simp⟩, ?_, ?_, fun a ha => hG.unit a ha.1, ?_⟩
  · intro a ha b hb
    refine ⟨hG.mul_mem a ha.1 b hb.1, ?_⟩
    rw [conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc aᴴ, ha.2, Matrix.one_mul, hb.2]
  · intro a ha
    refine ⟨hG.inv_mem a ha.1, ?_⟩
    rw [Matrix.inv_eq_left_inv ha.2, conjTranspose_conjTranspose]
    exact mul_eq_one_comm.mp ha.2
  · have hc : Continuous fun g : Mat k r => gᴴ * g :=
      (continuous_id.matrix_conjTranspose).matrix_mul continuous_id
    exact hG.closed.inter (isClosed_singleton.preimage hc)

theorem compact (k r : ℕ) : IsCompact (Kset k r) := by
  have hB : IsCompact (Set.pi Set.univ fun _ : Fin (2 * r + k + 1) =>
      Set.pi Set.univ fun _ : Fin (2 * r + k + 1) => Metric.closedBall (0 : ℂ) 1) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _
  refine IsCompact.of_isClosed_subset (s := (Set.pi Set.univ fun _ : Fin (2 * r + k + 1) =>
      Set.pi Set.univ fun _ : Fin (2 * r + k + 1) => Metric.closedBall (0 : ℂ) 1)) hB
      (closedSubgroup k r).closed ?_
  intro g hg i _ j _
  have hu : Matrix.of g ∈ Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ :=
    Matrix.mem_unitaryGroup_iff'.mpr hg.2
  simpa using entry_norm_bound_of_unitary hu i j

theorem hpk_mem (k r : ℕ) : Hpk k r ∈ Kset k r := by
  obtain ⟨h1, h2, -⟩ := hermitian_pos_facts_hold k r
  refine ⟨?_, by rw [h1, h2]⟩
  show (Hpk k r)ᴴ * Hpk k r * Hpk k r = Hpk k r
  rw [h1, h2, Matrix.one_mul]

theorem star_mem {k r : ℕ} {κ : Mat k r} (h : κ ∈ Kset k r) : κᴴ ∈ Kset k r := by
  have := (closedSubgroup k r).inv_mem κ h
  rwa [Matrix.inv_eq_left_inv h.2] at this

theorem comm_hpk {k r : ℕ} {κ : Mat k r} (h : κ ∈ Kset k r) : κ * Hpk k r = Hpk k r * κ := by
  have h1 : κᴴ * Hpk k r * κ = Hpk k r := h.1
  have h2 : κ * κᴴ = 1 := mul_eq_one_comm.mp h.2
  calc κ * Hpk k r = κ * (κᴴ * Hpk k r * κ) := by rw [h1]
    _ = (κ * κᴴ) * Hpk k r * κ := by simp only [Matrix.mul_assoc]
    _ = Hpk k r * κ := by rw [h2, Matrix.one_mul]

theorem sum_normSq_eq_trace {n : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) :
    ∑ i, ∑ j, Complex.normSq (g i j) = (trace (gᴴ * g)).re := by
  rw [Finset.sum_comm]
  simp only [trace, diag, Matrix.mul_apply, conjTranspose_apply, Complex.re_sum]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  simp [Complex.normSq_apply]

theorem gN_biinv {k r : ℕ} {κ κ' : Mat k r} (h : κ ∈ Kset k r) (h' : κ' ∈ Kset k r) (g : Mat k r) :
    gN (κ * g * κ') = gN g := by
  have h2 : κ' * κ'ᴴ = 1 := mul_eq_one_comm.mp h'.2
  unfold gN
  rw [sum_normSq_eq_trace, sum_normSq_eq_trace]
  have e : (κ * g * κ')ᴴ * (κ * g * κ') = κ'ᴴ * (gᴴ * g * κ') := by
    calc (κ * g * κ')ᴴ * (κ * g * κ') = κ'ᴴ * (gᴴ * (κᴴ * κ) * g * κ') := by
          simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = _ := by rw [h.2, Matrix.mul_one]
  rw [e, trace_mul_comm, Matrix.mul_assoc, h2, Matrix.mul_one]

theorem kset_facts : ∀ k r : ℕ, IsClosedSubgroup (Kset k r) ∧ IsCompact (Kset k r) ∧ Hpk k r ∈ Kset k r ∧ (∀ κ ∈ Kset k r, κᴴ ∈ Kset k r ∧ κ * Hpk k r = Hpk k r * κ) ∧ ∀ κ ∈ Kset k r, ∀ κ' ∈ Kset k r, ∀ g : Mat k r, gN (κ * g * κ') = gN g :=
  fun k r => ⟨closedSubgroup k r, compact k r, hpk_mem k r, fun _ h => ⟨star_mem h, comm_hpk h⟩,
    fun _ h _ h' g => gN_biinv h h' g⟩

end GlobalTheory.HCXi.KGroup
