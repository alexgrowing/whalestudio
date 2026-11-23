import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PlacesOverTypePrimeChosenAndConj
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OtherInstanceCharacterEqPsiSymmetricArgument
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TransportedFiniteCharacterInverseExpTrace
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.places_over_typePrime_chosen_and_conj : ∀ (D : D7) (k : Fin 2), Function.Injective (Sum.elim (D.naut.plGw k) (fun v => GlobalTheory.IdemSupport.cP (D := D) (D.naut.plGw k v))) ∧ (∀ W : HeightOneSpectrum (𝓞 D.host.E), ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ W.asIdeal ↔ ∃ i, Sum.elim (D.naut.plGw k) (fun v => GlobalTheory.IdemSupport.cP (D := D) (D.naut.plGw k v)) i = W) ∧ Fintype.card (D.nd.PlG k ⊕ D.nd.PlG k) = Module.finrank ℚ D.host.E := by
  first | exact @GlobalTheory.PlacesOverG.places_over_g_k | exact GlobalTheory.PlacesOverG.places_over_g_k | (intros; apply GlobalTheory.PlacesOverG.places_over_g_k <;> assumption)
