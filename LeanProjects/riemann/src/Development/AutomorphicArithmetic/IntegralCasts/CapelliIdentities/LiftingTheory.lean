import Mathlib
import Formalism.HermitianCurvature.WeylElementCommutesLevelOne
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.MapLeftMulVolumeEq
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.MapMulVolumeOfSubgroup

open Matrix in
private theorem hpk_sq (k r : ℕ) : Formalism.QuantumDeterminants.Hpk k r * Formalism.QuantumDeterminants.Hpk k r = 1 := by
  have key : ∀ i : Fin (2 * r + k + 1), ∃ s : Fin (2 * r + k + 1),
      (s.val = if r ≤ i.val ∧ i.val ≤ r + k then i.val else 2 * r + k - i.val) := fun i =>
    ⟨⟨if r ≤ i.val ∧ i.val ≤ r + k then i.val else 2 * r + k - i.val, by
      have := i.isLt; split_ifs <;> omega⟩, rfl⟩
  ext i l
  obtain ⟨s, hs⟩ := key i
  have hi := i.isLt
  have hl := l.isLt
  rw [Matrix.mul_apply, Finset.sum_eq_single s]
  · simp only [Formalism.QuantumDeterminants.Hpk, Matrix.one_apply, Fin.ext_iff]
    split_ifs at hs ⊢ <;> first | omega | norm_num
  · intro j _ hj
    have hj' : j.val ≠ s.val := fun h => hj (Fin.ext h)
    have hjl := j.isLt
    have : Formalism.QuantumDeterminants.Hpk k r i j = 0 := by
      simp only [Formalism.QuantumDeterminants.Hpk, Fin.ext_iff]
      split_ifs at hs ⊢ <;> first | omega | rfl
    rw [this, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ s) h

open Matrix in
private theorem norm_det_one (k r : ℕ) (g : Formalism.FourierDecayAlt.B.Mat k r) (hg : g ∈ Formalism.FourierDecayAlt.B.GV k r) :
    ‖g.det‖ = 1 := by
  have h1 : gᴴ * Formalism.QuantumDeterminants.Hpk k r * g = Formalism.QuantumDeterminants.Hpk k r := hg
  have h2 : (Formalism.QuantumDeterminants.Hpk k r).det ≠ 0 := by
    intro h
    have := congrArg Matrix.det (hpk_sq k r)
    rw [Matrix.det_mul, h, Matrix.det_one] at this
    simp at this
  have h3 := congrArg (fun m => ‖Matrix.det m‖) h1
  simp only [Matrix.det_mul, Matrix.det_conjTranspose, norm_mul, norm_star] at h3
  have h4 : ‖(Formalism.QuantumDeterminants.Hpk k r).det‖ ≠ 0 := norm_ne_zero_iff.mpr h2
  have h5 : ‖g.det‖ * ‖g.det‖ = 1 := by
    apply mul_left_cancel₀ h4
    linarith
  have h6 := norm_nonneg g.det
  nlinarith

theorem UpperTheory.Reformulated.B.LiftingTheory.volCrude :
    Formalism.FourierDecayAlt.B2.VolCrude := by
  intro k r μ h
  have hd : ∀ a ∈ (Formalism.FourierDecayAlt.B.GV k r : Set (Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → ℂ)),
      ‖(Matrix.of a).det‖ = 1 := fun a ha => norm_det_one k r a ha
  obtain ⟨C, hC⟩ := UpperTheory.map_mul_volume_of_subgroup (2 * r + k + 1) (Formalism.FourierDecayAlt.B.GV k r) μ h.conc hd
    (fun a ha => UpperTheory.map_left_mul_volume_eq _ a (hd a ha)) (fun a ha => h.left a ha) h.finite_compact
  refine ⟨C, fun R hR => ?_⟩
  have e : R ^ (2 * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2) = R ^ (2 * (2 * r + k + 1) ^ 2) := by
    rw [← Real.rpow_natCast R]
    congr 1
    push_cast
    ring
  rw [e]
  exact hC R hR
