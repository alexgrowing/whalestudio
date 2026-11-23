import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CmSubfieldsCompositumClosed
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RegPolOfRepOf
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.ArthurClozel
import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.AboveL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cm_subfields_compositum_closed : ∀ (Ω : Type) [Field Ω] (E : Type) [Field E] [NumberField E] [IsCMField E] [Algebra E Ω] [IsAlgClosure E Ω], (∀ (M N : IntermediateField E Ω) [NumberField M] [NumberField N] [NumberField ↥(M ⊔ N)], IsCMField M → IsCMField N → IsCMField ↥(M ⊔ N)) ∧ (∀ (M N : IntermediateField E Ω) [NumberField M] [NumberField N], N ≤ M → IsCMField M → IsCMField N) ∧ ∀ (M : IntermediateField E Ω) [NumberField M] (S : Set Ω), (∀ x ∈ S, ∀ φ : Ω →+* ℂ, (φ x).im = 0) → M = IntermediateField.adjoin E S → IsCMField M := by
  first | exact @GlobalTheory.CMSub.isCMField_sup_le_adjoin | exact GlobalTheory.CMSub.isCMField_sup_le_adjoin | (intros; apply GlobalTheory.CMSub.isCMField_sup_le_adjoin <;> assumption)
