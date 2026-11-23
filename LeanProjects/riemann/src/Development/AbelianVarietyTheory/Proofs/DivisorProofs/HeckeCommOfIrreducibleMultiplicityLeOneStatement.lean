import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCommOfIrreducibleMultiplicityLeOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigCongr
open GlobalTheory.FinGL GlobalTheory.FinGL.LeviWh Formalism.L2.DIV Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hecke_comm_of_irreducible_multiplicity_le_one : ∀ (H : Type) [Group H] [Finite H] (U : Subgroup H) (χ : H → ℂ), (∀ x ∈ U, ∀ y ∈ U, χ (x * y) = χ x * χ y) → χ 1 = 1 → (∀ (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (τ : Representation ℂ H W), τ.IsIrreducible → finrank ℂ (eig τ (U : Set H) χ) ≤ 1) → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (τ : Representation ℂ H V), ∃ e : Module.End ℂ V, e * e = e ∧ (∀ v ∈ eig τ (U : Set H) χ, e v = v) ∧ (∀ T : Module.End ℂ V, (∀ g, Commute T (τ g)) → Commute T e) ∧ ∀ g h : H, e * τ g * e * τ h * e = e * τ h * e * τ g * e := by
  first | exact @GlobalTheory.FinGL.LeviWh.exists_idem_hecke_comm | exact GlobalTheory.FinGL.LeviWh.exists_idem_hecke_comm | (intros; apply GlobalTheory.FinGL.LeviWh.exists_idem_hecke_comm <;> assumption)
