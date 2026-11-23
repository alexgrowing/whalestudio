import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryQuotientCompactness.ExistsModularFunction
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryQuotientCompactness.UnipotentRadicalContracting
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryQuotientCompactness.IsCompactInterUnitBox

open MeasureTheory Matrix

noncomputable section

namespace PI.NUnimodLoc.UnitaryGroupMassFormula

open PI PI.QuotSetU PI.QuotSetU.UnitaryGroupMassFormula PI.QuotSetU.UnitaryGroupMassFormula.SW

def NStdUnimod : Prop :=
  ∀ k r : ℕ, ∀ μ : Measure (MtM (2 * r + k + 1)), IsHaarOnM (Nset k r) μ → IsRightInvM (Nset k r) μ

theorem nset_isMatGroup (k r : ℕ) : IsMatGroup (Nset k r) :=
  ⟨isClosed_N, (nilpotent_subgroup k r).1, (nilpotent_subgroup k r).2.1,
    fun a ha => ⟨(nilpotent_subgroup k r).2.2 a ha, mul_inv_UH ha.1⟩⟩

theorem dS_conj_N_iff {k r : ℕ} {s : ℝ} (hs : s ≠ 0)
    (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    dS k r s * g * (dS k r s)⁻¹ ∈ Nset k r ↔ g ∈ Nset k r := by
  constructor
  · intro h
    rw [dS_inv_eq hs] at h
    have h2 := dS_conj_N (inv_ne_zero hs) h
    rw [inv_inv] at h2
    have h1' := dS_mul_dS_inv (k := k) (r := r) (inv_ne_zero hs)
    rw [inv_inv] at h1'
    have e : dS k r s⁻¹ * (dS k r s * g * dS k r s⁻¹) * dS k r s = g := by
      simp only [Matrix.mul_assoc]
      rw [h1', Matrix.mul_one, ← Matrix.mul_assoc, h1', Matrix.one_mul]
    rwa [e] at h2
  · intro h
    rw [dS_inv_eq hs]
    exact dS_conj_N hs h

theorem exists_conj_box {k r : ℕ} {n : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hn : n ∈ Nset k r) :
    ∃ s : ℝ, 0 < s ∧ ∀ i j, ‖(dS k r s * n * (dS k r s)⁻¹ - 1) i j‖ ≤ 1 := by
  set M : ℝ := ∑ i, ∑ j, ‖n i j‖ + 1 with hM
  have h0 : 0 ≤ ∑ i, ∑ j, ‖n i j‖ := by positivity
  have hM1 : 1 ≤ M := by linarith
  have hMp : 0 < M := by linarith
  refine ⟨1 / M, div_pos one_pos hMp, fun i j => ?_⟩
  have hs1 : 1 / M ≤ 1 := by rw [div_le_one hMp]; exact hM1
  refine (norm_dS_conj_le (div_pos one_pos hMp) hs1 hn i j).trans ?_
  have h1 : ‖n i j‖ ≤ ∑ j', ‖n i j'‖ :=
    Finset.single_le_sum (f := fun j' => ‖n i j'‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ j)
  have h2 : ∑ j', ‖n i j'‖ ≤ ∑ i', ∑ j', ‖n i' j'‖ :=
    Finset.single_le_sum (f := fun i' => ∑ j', ‖n i' j'‖) (fun _ _ => by positivity) (Finset.mem_univ i)
  have hle : ‖n i j‖ ≤ M := by linarith
  rw [one_div, inv_mul_le_iff₀ hMp, mul_one]
  exact hle

theorem nonstandard_unimodular_lattice : NStdUnimod := by
  intro k r μ hμ
  have hG := nset_isMatGroup k r
  obtain ⟨D, hD, hR⟩ := exists_modular_function _ (Nset k r) hG
  have hle : ∀ n ∈ Nset k r, D n ≤ 1 := by
    intro n hn
    obtain ⟨M, hM⟩ := hD.2.2.2 (Nset k r ∩ box1 _) Set.inter_subset_left (isCompact_inter_unit_box hG.1)
    apply le_one_of_pow_le (M := M)
    intro p
    have hnp : n ^ p ∈ Nset k r := pow_mem hG hn p
    obtain ⟨s, hs0, hbox⟩ := exists_conj_box hnp
    have hc : IsUnit (dS k r s) :=
      (Matrix.isUnit_iff_isUnit_det _).2 (Matrix.isUnit_det_of_right_inverse (dS_mul_dS_inv hs0.ne'))
    have hcG : ∀ g, dS k r s * g * (dS k r s)⁻¹ ∈ Nset k r ↔ g ∈ Nset k r :=
      fun g => dS_conj_N_iff hs0.ne' g
    rw [← modPow hG hD hn p, ← hD.2.2.1 _ hc hcG _ hnp]
    exact hM _ ⟨(hcG _).2 hnp, hbox⟩
  exact hR (fun n hn => modEqOne hG hD hn (hle n hn) (hle _ ((nilpotent_subgroup k r).2.2 _ hn))) μ hμ

end PI.NUnimodLoc.UnitaryGroupMassFormula
