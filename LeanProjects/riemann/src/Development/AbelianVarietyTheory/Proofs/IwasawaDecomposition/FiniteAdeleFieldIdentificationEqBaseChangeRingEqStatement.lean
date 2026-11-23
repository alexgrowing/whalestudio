import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteAdeleFieldIdentificationEqBaseChangeRingEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftsInvOne
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteAdeleFieldIdentification_eq_baseChangeRingEquiv : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (ι : AfE F E ≃+* FiniteAdeleRing (𝓞 E) E), GlobalTheory.TwU.IsAdIso ι → ∀ x, ι x = afIso F E x := by
  first | exact @GlobalTheory.isAdIso_eq_afIso | exact GlobalTheory.isAdIso_eq_afIso | (intros; apply GlobalTheory.isAdIso_eq_afIso <;> assumption)
