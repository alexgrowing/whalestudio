import Mathlib
import CompanionTheory.AutomorphicTheory.PieriRules.PieriDegreeBounds.Imports
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.NumericalFamilyShapeGapsStatement
import CompanionTheory.AutomorphicTheory.PieriRules.PieriDegreeBounds.NumericalFamilyShapeGaps
import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.TensorDecompositionInjectiveParametersStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsFRepDualStandardUnitaryRepStatement
import CompanionTheory.AutomorphicTheory.PieriRules.PieriDegreeBounds.IsFRepDualStandardUnitaryRep
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsFRepExteriorPowerStandardRepStatement
import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.IsDSOfIsDG

namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.TensExists

theorem l1_add_le {n : ℕ} (x y : Fin n → ℤ) : n1 (x + y) ≤ n1 x + n1 y := by
  unfold n1
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun i _ => Int.natAbs_add_le _ _

theorem l1_sub_le {n : ℕ} (x y : Fin n → ℤ) : n1 (x - y) ≤ n1 x + n1 y := by
  unfold n1
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun i _ => Int.natAbs_sub_le _ _

theorem n1_eZ_eq_card {n : ℕ} (I : Finset (Fin n)) : n1 (eZ I) = I.card := by
  unfold n1 eZ
  have : ∀ i : Fin n, (if i ∈ I then (1 : ℤ) else 0).natAbs = if i ∈ I then 1 else 0 := by
    intro i; split_ifs <;> rfl
  simp [this]

theorem l1_single {n : ℕ} (s : Fin n) : n1 (Pi.single s (1 : ℤ)) = 1 := by
  unfold n1
  rw [Finset.sum_eq_single s]
  · simp
  · intro b _ hb; simp [hb]
  · simp

theorem addSet_inj {n l : ℕ} (mu : Fin n → ℝ) : Function.Injective (fun I : Sub n l => addSet mu I.1) := by
  intro I J hIJ
  apply Subtype.ext
  ext a
  have h := congrFun hIJ a
  simp only [addSet, add_right_inj] at h
  by_cases h1 : a ∈ I.1 <;> by_cases h2 : a ∈ J.1 <;> simp_all

theorem sub_single_inj {n : ℕ} (mu : Fin n → ℝ) :
    Function.Injective (fun s : Fin n => mu - (Pi.single s 1 : Fin n → ℝ)) := by
  intro s t hst
  by_contra hne
  have h := congrFun hst s
  simp [Pi.single_apply, hne] at h

theorem tens_exists : HypsG → ∀ (k r : ℕ) (lam : Fin (2 * r + k + 1) → ℝ) (u : ℕ → ℝ) (b bv ga h : ℝ) (q0 : ℕ) (R : (Fin (2 * r + k + 1) → ℤ) → Rep k r), Num k r lam u b bv ga h q0 → IsFamG lam q0 R → ∀ ν, (∀ l, n1 ν + l ≤ q0 → ∃ io pr ep, TensH (cmp l) (cmp l (Formalism.QuantumDeterminants.Hpk k r)) (R ν) (fun I : Sub (2 * r + k + 1) l => R (ν + eZ I.1)) io pr ep) ∧ (n1 ν + 1 ≤ q0 → ∃ io pr ep, TensH dualM (Formalism.QuantumDeterminants.Hpk k r) (R ν) (fun s => R (ν - Pi.single s 1)) io pr ep) := by
  intro hH k r lam u b bv ga h q0 R hN hF ν
  have hZ : ZuckG := hH.2.2.2.2.1
  have hnum := (GlobalTheory.T.numericalFamily_shape_gaps k r lam u b bv ga h q0 hN).2 ν
  constructor
  · intro l hl
    have h0 : n1 ν ≤ q0 := by omega
    have hR := hF ν h0
    have hI : ∀ I : Sub (2 * r + k + 1) l, (R (ν + eZ I.1)).IsDG (PI.BesselPeriodGGP.eps48 k r)
        (addSet (fun a => lam a + (ν a : ℝ)) I.1) := by
      intro I
      have h1 : n1 (ν + eZ I.1) ≤ q0 := by
        have := l1_add_le ν (eZ I.1)
        rw [n1_eZ_eq_card, I.2] at this
        omega
      have h2 := hF _ h1
      have e : (fun a => lam a + (((ν + eZ I.1) a : ℤ) : ℝ)) = addSet (fun a => lam a + (ν a : ℝ)) I.1 := by
        funext a
        simp only [addSet, eZ, Pi.add_apply]
        split_ifs <;> push_cast <;> ring
      rwa [e] at h2
    obtain ⟨io, pr, hT⟩ := (hZ k r _ lam q0 R hF ν).1 l hl
    exact GlobalTheory.T.tensor_decomposition_injective_parameters hH k r _ _ _ _ l _ _ io pr _ _ _ hR hI (addSet_inj _) (GlobalTheory.T.isFRep_exteriorPower_standardRep k r l) hT
  · intro hl
    have h0 : n1 ν ≤ q0 := by omega
    have hR := hF ν h0
    have hI : ∀ s : Fin (2 * r + k + 1), (R (ν - Pi.single s 1)).IsDG (PI.BesselPeriodGGP.eps48 k r)
        ((fun a => lam a + (ν a : ℝ)) - Pi.single s 1) := by
      intro s
      have h1 : n1 (ν - Pi.single s 1) ≤ q0 := by
        have := l1_sub_le ν (Pi.single s 1)
        rw [l1_single] at this
        omega
      have h2 := hF _ h1
      have e : (fun a => lam a + (((ν - Pi.single s 1 : Fin (2 * r + k + 1) → ℤ) a : ℤ) : ℝ)) =
          (fun a => lam a + (ν a : ℝ)) - Pi.single s 1 := by
        funext a
        simp only [Pi.sub_apply, Pi.single_apply]
        split_ifs <;> push_cast <;> ring
      rwa [e] at h2
    obtain ⟨io, pr, hT⟩ := (hZ k r _ lam q0 R hF ν).2 hl
    exact GlobalTheory.T.tensor_decomposition_injective_parameters hH k r _ _ _ _ 1 _ _ io pr _ _ _ hR hI (sub_single_inj _) (GlobalTheory.T.isFRep_dual_standard_unitaryRep k r) hT

end GlobalTheory.TensExists
