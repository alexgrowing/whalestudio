import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.QuantumDeterminantCommute.Development
import Formalism.RealPlaceAnalysis.ThirdArithmeticHolds

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q

noncomputable section

namespace QmCapCommW

theorem quantum_determinant_commutes : QdetCommute := by
  intro A _ _ n E hE u v
  have hc : ∀ c d, Commute (qdet E u) (E c d) := fun c d => qDetCentral A n E hE u c d
  have hT : ∀ w a b, Commute (qdet E u) (Tm E w a b) := by
    intro w a b
    unfold Tm
    refine Commute.add_right ?_ (hc a b)
    split_ifs
    · exact Algebra.commute_algebraMap_right w _
    · exact Commute.zero_right _
  have key : Commute (qdet E u) (qdet E v) := by
    show Commute (qdet E u) (∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : A) *
      (List.ofFn fun k : Fin n => Tm E (v - (k : ℂ)) (id (σ k)) (id k)).prod)
    refine Commute.sum_right _ _ _ fun σ _ => ?_
    refine Commute.mul_right Commute.intCast_right ?_
    refine Commute.list_prod_right _ _ fun y hy => ?_
    simp only [List.mem_ofFn] at hy
    obtain ⟨k, rfl⟩ := hy
    exact hT _ _ _
  exact key.eq

end QmCapCommW
