import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RestrictedTensorBasePointNormSq
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIntOv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinPartAlgebraMap

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PlaceTensor

theorem idem_eq_locIdem (D : D7) (p : Place D) : idem D p = GlobalTheory.LocWeil.idem D p := by
  rcases p with v | τ
  · rw [GlobalTheory.LocWeil.PlaceIdem.idem_inl]
    rfl
  · rw [GlobalTheory.LocWeil.PlaceIdem.idem_inr]
    simp only [idem, GlobalTheory.LocWeil.PlaceIdem.eInf]
    congr 2

theorem idem_spec : ∀ D : D7, (∀ p, idem D p * idem D p = idem D p) ∧ (∀ p q, p ≠ q → idem D p * idem D q = 0) ∧ (∀ p, cA D (idem D p) = idem D p) ∧ (∀ v : FinPl D, infPart D (idem D (.inl v)) = 0 ∧ finPart D (idem D (.inl v)) ∈ intAE D ∧ IsPlaceIdem D v (pairA D.host.F 0 (singleV D.host.F v 1))) ∧ (∀ τ : D.what₂.Tau, finPart D (idem D (.inr τ)) = 0) ∧ infPart D (∑ τ : D.what₂.Tau, idem D (.inr τ)) = 1 ∧ ∀ θ : InfFam D, IsInfFam θ → ∀ τ : D.what₂.Tau, θ τ (infPart D (idem D (.inr τ))) = 1 ∧ ∀ τ' : D.what₂.Tau, τ' ≠ τ → θ τ (infPart D (idem D (.inr τ'))) = 0 := by
  intro D
  have hE : ∀ p, idem D p = GlobalTheory.LocWeil.idem D p := idem_eq_locIdem D
  obtain ⟨hOrth, hTheta, hFinInf, hSum, -, -⟩ := GlobalTheory.LocWeil.PlaceIdem.idem_props D
  simp only [hE]
  refine ⟨fun p => GlobalTheory.LocWeil.idem_mul_self p, fun p q hpq => hOrth p q hpq, fun p => GlobalTheory.LocWeil.cA_idem p,
    ?_, hFinInf, hSum, ?_⟩
  · intro v
    rw [GlobalTheory.LocWeil.PlaceIdem.idem_inl, GlobalTheory.LocWeil.PlaceIdem.infPart_algebraMap,
      GlobalTheory.LocWeil.PlaceIdem.finPart_algebraMap]
    refine ⟨?_, ?_, ⟨singleV D.host.F v 1, rfl, GlobalTheory.LocWeil.PlaceIdem.evalV_single_same _ v,
      fun v' h => GlobalTheory.LocWeil.PlaceIdem.evalV_single_ne _ h⟩⟩
    · exact TensorProduct.zero_tmul _ _
    · apply AddSubgroup.subset_closure
      refine ⟨singleV D.host.F v 1, ?_, 1, ?_⟩
      · simp only [intAf, Set.mem_setOf_eq]
        intro u
        rcases eq_or_ne u v with rfl | h
        · rw [GlobalTheory.LocWeil.PlaceIdem.evalV_single_same]
          exact one_mem _
        · rw [GlobalTheory.LocWeil.PlaceIdem.evalV_single_ne _ h]
          exact zero_mem _
      · rfl
  · intro θ hθ τ
    refine ⟨?_, fun τ' h => ?_⟩
    · rw [hTheta θ hθ τ τ, if_pos rfl]
    · rw [hTheta θ hθ τ' τ, if_neg (Ne.symm h)]

end GlobalTheory.PlaceTensor
