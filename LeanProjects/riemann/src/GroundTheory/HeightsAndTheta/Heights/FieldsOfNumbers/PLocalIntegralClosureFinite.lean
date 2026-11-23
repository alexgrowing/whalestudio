import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsLocalIntegralClosureFinite
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsNoetherIntegralClosure
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsFunctionFieldFinite
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsDegZeroLocFrac
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PSemilocalFiniteRank
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PPFDegree
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.LocalIntegralClosureChart
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

theorem LocalIntegralClosureFinite.proof (hN : NoetherIntegralClosureFinite.Statement.{u})
    (hF : FunctionFieldFinite.Statement.{u}) (hQ : DegZeroLocQuot.Statement.{u})
    (hD : MChartDehomog.Statement.{u}) (hFr : DegZeroLocFrac.Statement.{u}) :
    LocalIntegralClosureFinite.Statement.{u} := by
  intro F _ K K' _ _ _ _ j ι' _ P' hP' hdim W hW hle
  have := hP'.isPrime
  have := hW.isPrime
  set P := contractPrime j P'
  set φ := contractFracMap j P'
  set A' := (degZeroLoc P {W}).map φ
  set L := homFracDegZero P'
  choose u hu using hW.relevant
  obtain ⟨hRA, hloc⟩ := degZeroLoc_map_eq_mul_inv hQ hD P W hle u hu φ
  set S := Set.range fun v => φ (chartMap P u (X v))
  have hAL : ∀ a ∈ A', a ∈ L := by
    rintro _ ⟨a, ha, rfl⟩
    exact map_homFracDegZero_le j ι' P' ⟨a, mem_homFracDegZero_of_mem_degZeroLoc P {W} a ha, rfl⟩
  have hEL : IntermediateField.adjoin F S ≤ L :=
    IntermediateField.adjoin_le_iff.mpr fun _ hx => hAL _ (hRA (Algebra.subset_adjoin hx))
  have hAE : ∀ a ∈ A', a ∈ IntermediateField.adjoin F S := fun a ha => by
    obtain ⟨r, hr, d, hd, -, -, rfl⟩ := hloc a ha
    exact mul_mem (IntermediateField.algebra_adjoin_le_adjoin F S hr)
      (inv_mem (IntermediateField.algebra_adjoin_le_adjoin F S hd))
  have hκE : (homFracDegZero P).map φ ≤ IntermediateField.adjoin F S := by
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨y, hy, w, hw, -, rfl⟩ := hFr F K (fun k => ι' (j k)) P
      (isMultiProjPrime_contractPrime j ι' hP') {W} (Set.finite_singleton W)
      (fun W' h => by rw [Set.mem_singleton_iff.mp h]; exact hW) z hz
    rw [map_div₀]
    exact div_mem (hAE _ ⟨y, hy, rfl⟩) (hAE _ ⟨w, hw, rfl⟩)
  have hdeg : IntermediateField.relfinrank ((homFracDegZero P).map φ) L ≠ 0 :=
    hF F K K' j ι' P' hP' hdim
  rw [← IntermediateField.relfinrank_mul_relfinrank hκE hEL,
    IntermediateField.relfinrank_eq_finrank_of_le hEL] at hdeg
  exact exists_finset_integral_span hN (Set.finite_range _) A' L hRA hloc hEL
    (FiniteDimensional.of_finrank_pos (Nat.pos_of_ne_zero (right_ne_zero_of_mul hdeg)))

end

end GroundTheory.Heights₂.Heights.FieldNumbers
