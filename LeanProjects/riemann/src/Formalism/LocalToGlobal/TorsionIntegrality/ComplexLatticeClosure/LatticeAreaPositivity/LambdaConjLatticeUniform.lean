import Formalism.LocalToGlobal.TorsionIntegrality.ComplexLatticeClosure.LamConjLat0
import Formalism.LocalToGlobal.TorsionIntegrality.ComplexLatticeClosure.LatticeAreaPositivity.Bridge
import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.WeierstrassUniqueness.UniqInvHolds
import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.ConjugateSets.Status

noncomputable section

namespace Formalism.L2.Th1.F2

open NumberField
open scoped Pointwise
open Formalism.BasicNotions (D7)
open Formalism.L2.GlobalTheoryTheory Formalism.MainNotions
open Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5

theorem lambda_of_lattice_holds : LamOfLat := by
  intro D cc δ hcc hδ
  exact lattice_ideal_lattice_holds D.host.K D.host.d (discriminant_mod_four D) ⟨D.host.sqrtMinusD, br_sqrt_mem D⟩
    (br_sqrt_sq D) (br_finrank_K D) (brPhi D) cc δ hcc hδ

variable [Fact _root_.Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.CMConjSetF] in
theorem lattice_ideal_conj_holds : LatIConj := by
  intro K _ _ d _ hd4 x hx hK φ 𝔞 δ h𝔞 hdisc M _ h2 h3 ρ
  have hδ0 : δ ≠ 0 := brcc_discr_delta_ne K φ 𝔞 δ hdisc
  have hjδ : IntegralLatticeDensity.jL (latI φ 𝔞 1) = IntegralLatticeDensity.jL (latI φ 𝔞 δ) := by
    rw [latI_eq_smul _ _ δ, br_jL_smul _ _ hδ0]
  have hjM : IntegralLatticeDensity.jL (latI φ 𝔞 δ) ∈ M := by
    rw [br_jL_eq]
    have hd1 : discr (latI φ 𝔞 δ) = 1 := hdisc
    rw [hd1, div_one]
    have h0 : (1728 : ℂ) ∈ M := by simp
    exact M.mul_mem h0 (M.pow_mem h2 3)
  have hjM1 : IntegralLatticeDensity.jL (latI φ 𝔞 1) ∈ M := by rw [hjδ]; exact hjM
  obtain ⟨𝔟, h𝔟, hρ⟩ := (ComplexMultiplicationLFunction.cmConjSetF_proved K d hd4 x hx hK φ 𝔞 h𝔞 M hjM1).1 ρ
  have hj : ρ ⟨IntegralLatticeDensity.jL (latI φ 𝔞 δ), hjM⟩ = IntegralLatticeDensity.jL (latI φ 𝔟 1) := by
    rw [← hρ]; congr 2; exact hjδ.symm
  obtain ⟨c, hc0, hlc, -⟩ := br_lamConj_eq uniqInv_holds M ρ (latI φ 𝔞 δ) (latI φ 𝔟 1) h2 h3 hdisc
    (discr_latI_ne_zero K d hd4 x hx hK φ 𝔟 h𝔟) hjM hj
  obtain ⟨h1, h2'⟩ := lattice_ideal_lattice_holds K d hd4 x hx hK φ 𝔟 1 h𝔟 one_ne_zero
  rw [hlc]
  exact ⟨is_lattice_smul_holds _ c hc0 h1, has_cm_smul_holds _ _ c h2'⟩

variable [Fact _root_.Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.CMConjSetF] in
theorem lambda_conj_lattice_uniform : LamConjLat0 := fun D => lambda_conj_lattice_holds D uniqInv_holds (ComplexMultiplicationLFunction.cmConjSet_holds D)

variable [Fact _root_.Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.CMConjSetF] in
theorem lambda_conj_theta_uniform : LamConjTheta0 := fun D => lambda_conj_theta_holds D uniqInv_holds (ComplexMultiplicationLFunction.cmConjSet_holds D)

end Formalism.L2.Th1.F2
