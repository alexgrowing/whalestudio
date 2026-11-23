import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnramifiedCmData
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CombineApply
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Matrix TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unramified_cm_data : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x), IsCMExt F E σ → Algebra.Unramified (𝓞 F) (𝓞 E) → @Formalism.BasicNotions.CMData F E _ _ _ _ (GlobalTheory.ThKUTr.starOf σ hσ) _ := by
  first | exact @GlobalTheory.ThKUTr.cmData_starOf | exact GlobalTheory.ThKUTr.cmData_starOf | (intros; apply GlobalTheory.ThKUTr.cmData_starOf <;> assumption)
