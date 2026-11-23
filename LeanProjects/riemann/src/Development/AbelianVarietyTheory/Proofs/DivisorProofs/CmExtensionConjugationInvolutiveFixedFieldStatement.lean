import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmExtensionConjugationInvolutiveFixedField
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntFOneMul
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF GlobalTheory.HeckeExtend
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cmExtension_conjugation_involutive_fixedField : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → (∀ x, σ (σ x) = x) ∧ ∀ x, σ x = x → ∃ f : F, algebraMap F E f = x := by
  first | exact @GlobalTheory.CMConjInvol.cm_conj_invol_fixed | exact GlobalTheory.CMConjInvol.cm_conj_invol_fixed | (intros; apply GlobalTheory.CMConjInvol.cm_conj_invol_fixed <;> assumption)
