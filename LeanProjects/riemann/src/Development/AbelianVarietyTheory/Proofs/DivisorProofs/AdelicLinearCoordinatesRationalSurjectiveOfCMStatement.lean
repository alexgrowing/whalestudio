import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicLinearCoordinatesRationalSurjectiveOfCM
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTransportF
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoMulInvOf
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicLinearCoordinates_rational_surjective_of_CM : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (nS nT N : ℕ)
    (e : Formalism.IndefR.DatumF.WOF F E nS nT ≃ₗ[AF F] GlobalTheory.ThetaTransform.VA F N),
    (∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : Fin N → F, e (Formalism.IndefR.DatumF.ratWF x) = (GlobalTheory.SWQ.rat y, GlobalTheory.SWQ.rat z)) →
    ∀ y z : Fin N → F, ∃ x : Matrix (Fin nT) (Fin nS) E, e (Formalism.IndefR.DatumF.ratWF x) = (GlobalTheory.SWQ.rat y, GlobalTheory.SWQ.rat z) := by
  first | exact @GlobalTheory.WeilSchrodinger.rat_onto_of_rat_maps_F | exact GlobalTheory.WeilSchrodinger.rat_onto_of_rat_maps_F | (intros; apply GlobalTheory.WeilSchrodinger.rat_onto_of_rat_maps_F <;> assumption)
