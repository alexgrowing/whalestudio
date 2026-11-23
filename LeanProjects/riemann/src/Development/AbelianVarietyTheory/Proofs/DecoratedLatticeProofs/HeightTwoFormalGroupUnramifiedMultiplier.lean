import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EndOmega
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsHondaTypeEvenFrobeniusPowersStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeightTwoHondaTypeFirstCoeffNormEqOneStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HondaTypeReductionToOneTermStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsUnitSolutionTwistedFrobeniusSquareStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HondaFunctionalEquationOneTermTypeStatement

open PowerSeries GlobalTheory.Honda Formalism.L2.Th1.CM

namespace GlobalTheory.Honda

theorem heightTwo_unitTwist : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] [CompleteSpace K]
    (l : ℕ) (σ : K →+* K), Unr K l σ → ResAlg K → ∀ (f e : K⟦X⟧), IntLog f e → ∀ w : K,
    CoefLe 1 (Formalism.L2.Th1.C.mulBy f e w) → σ (σ w) = w → ‖σ w - w‖ = 1 →
    (∃ n, n ≤ l ^ 2 ∧ ‖coeff n (Formalism.L2.Th1.C.mulBy f e (l : K))‖ = 1) →
    ∃ ε : K, ‖ε‖ = 1 ∧ CoefLe 1 (e.subst (C ε * ltLog K l)) := by
  intro K _ _ _ _ l σ hU hR f e hI w hw hσw hw1 hht
  obtain ⟨c, hc1, hc⟩ := GlobalTheory.T.exists_hondaType_evenFrobeniusPowers K l σ hU f e hI w hw hσw hw1
  have hc0 : ‖c 0‖ = 1 := GlobalTheory.T.height_two_hondaType_first_coeff_norm_eq_one K l σ hU f e hI c hc1 hc hht
  have hq : 2 ≤ l ^ 2 := by
    have h2 : 2 ≤ l := hU.1.two_le
    nlinarith
  have hτ : ∀ x, ‖(σ ^ 2) x‖ = ‖x‖ := by
    intro x
    rw [pow_two, RingHom.mul_def, RingHom.comp_apply, hU.2.2.2.2.1, hU.2.2.2.2.1]
  obtain ⟨c', hc'1, hc'⟩ := GlobalTheory.T.hondaType_reduction_to_one_term K l (l ^ 2) (σ ^ 2) hq hU.2.2.1 hτ f hI.1.1 c hc1 hc0 hc
  obtain ⟨ε, hε1, hε⟩ := GlobalTheory.T.exists_unit_solution_twisted_frobenius_square K l σ hU hR c' hc'1
  exact ⟨ε, hε1, GlobalTheory.T.honda_functional_equation_one_term_type K l σ hU f e hI.1 c' ε hε1 hε hc'⟩

end GlobalTheory.Honda
