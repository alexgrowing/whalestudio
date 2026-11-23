import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.EisensteinGrowthForms.GrowForms
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup

noncomputable section

namespace GlobalTheory.EisBL.AETop

open NumberField IsDedekindDomain Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

instance fdAE : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E

instance modTopAE : IsModuleTopology (AF F) (AE F E) := ⟨rfl⟩

instance ringAE : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _

theorem nonempty_homeomorphAE : Nonempty (AE F E ≃ₜ (Fin (Module.finrank F E) → AF F)) :=
  GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (AF F)

instance t2AE : T2Space (AE F E) := by
  have := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  obtain ⟨e⟩ := nonempty_homeomorphAE (F := F) (E := E)
  exact e.isEmbedding.t2Space

instance locCompactAE : LocallyCompactSpace (AE F E) := by
  have := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele F
  obtain ⟨e⟩ := nonempty_homeomorphAE (F := F) (E := E)
  exact e.isClosedEmbedding.locallyCompactSpace

instance secondCountableAE : SecondCountableTopology (AE F E) := by
  have := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  obtain ⟨e⟩ := nonempty_homeomorphAE (F := F) (E := E)
  exact e.secondCountableTopology

instance topGrpGL {ι : Type} [Fintype ι] [DecidableEq ι] : IsTopologicalGroup (GL ι (AE F E)) := inferInstance

instance isTopologicalGroup_G2 {σ : E →ₐ[F] E} {n : ℕ} {Y : Spc F E n} : IsTopologicalGroup (G2 σ Y) := inferInstance

end GlobalTheory.EisBL.AETop
