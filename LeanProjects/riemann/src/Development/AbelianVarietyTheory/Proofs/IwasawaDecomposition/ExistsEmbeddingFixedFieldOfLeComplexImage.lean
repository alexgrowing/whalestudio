import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenUsedOfCenReal
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SettingsFormsExistList
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem exists_embedding_fixedField_of_le_complexImage : ∀ (s : Stages) (M : IntermediateField ℚ ℂ), M ≤ s.B.fixedCoefficientFieldInComplex → ∃ j : M →+* s.toD7.LL0, (embLL0 s.toD7).comp j = M.val.toRingHom := by
  intro s M hle
  let e := IntermediateField.equivMap s.B.LL0 s.B.embLL.toRatAlgHom
  refine ⟨(e.symm.toAlgHom.toRingHom).comp (IntermediateField.inclusion hle).toRingHom, ?_⟩
  ext x
  show s.B.embLL ((e.symm ⟨x.1, hle x.2⟩ : s.B.LL0) : _) = x.1
  exact congrArg Subtype.val (e.apply_symm_apply ⟨x.1, hle x.2⟩)

end GlobalTheory
