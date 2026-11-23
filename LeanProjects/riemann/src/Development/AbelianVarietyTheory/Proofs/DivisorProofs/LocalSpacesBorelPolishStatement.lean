import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalSpacesBorelPolish
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StabAtPair
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.LemF
open GlobalTheory.Doubling (absE)
open GlobalTheory.ThK.LemF.QuotInv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_spaces_borel_polish : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (m : ℕ) (v : Pl F),
    (LocallyCompactSpace (vecAt F E m (evFin F v)) ∧ SecondCountableTopology (vecAt F E m (evFin F v)) ∧
      T2Space (vecAt F E m (evFin F v)) ∧ BorelSpace (vecAt F E m (evFin F v))) ∧
    (LocallyCompactSpace (skewAt σ (evFin F v)) ∧ SecondCountableTopology (skewAt σ (evFin F v)) ∧
      T2Space (skewAt σ (evFin F v)) ∧ BorelSpace (skewAt σ (evFin F v))) := by
  first | exact @GlobalTheory.ThK.LemF.QuotInv.Facts.vecAt_skewAt_facts | exact GlobalTheory.ThK.LemF.QuotInv.Facts.vecAt_skewAt_facts | (intros; apply GlobalTheory.ThK.LemF.QuotInv.Facts.vecAt_skewAt_facts <;> assumption)
