import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.FullySplitStabilizers
import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.HermitianMassFormula
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SgAlg GlobalTheory.IndefiniteRowSideFullHecke
open scoped TensorProduct ENNReal

namespace GlobalTheory.ArchUnitaryTop

theorem top_facts : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n a : ℕ) (J : Matrix (Fin n) (Fin n) E), ContinuousSMul (HA (Ainf F) σ J) (Fin a → Fin n → Ainf F ⊗[F] E) ∧ BorelSpace (Fin a → Fin n → Ainf F ⊗[F] E) ∧ SecondCountableTopology (Fin a → Fin n → Ainf F ⊗[F] E) ∧ T2Space (Fin a → Fin n → Ainf F ⊗[F] E) ∧ IsTopologicalGroup (HA (Ainf F) σ J) ∧ LocallyCompactSpace (HA (Ainf F) σ J) ∧ SecondCountableTopology (HA (Ainf F) σ J) ∧ T2Space (HA (Ainf F) σ J) := by
  intro F E _ _ _ _ _ σ n a J
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_infiniteAdele F
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_infiniteAdeleRing_of_numberField_field F
  haveI : IsModuleTopology (Ainf F) (Ainf F ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (Ainf F ⊗[F] E) := IsModuleTopology.isTopologicalRing (Ainf F) _
  obtain ⟨e⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (Ainf F)
  haveI : SecondCountableTopology (Ainf F ⊗[F] E) := e.secondCountableTopology
  haveI : T2Space (Ainf F ⊗[F] E) := e.isEmbedding.t2Space
  haveI : BorelSpace (Ainf F ⊗[F] E) := ⟨rfl⟩
  obtain ⟨h1, h2, h3⟩ := GlobalTheory.AdelicUnitaryTop.lcsc_HA (Ainf F) σ n J
  refine ⟨⟨?_⟩, inferInstance, inferInstance, inferInstance,
    inferInstanceAs (IsTopologicalGroup (HR (Ainf F) σ J)), h1, h2, h3⟩
  have hm : Continuous fun g : HA (Ainf F) σ J => HA.mat (Ainf F) σ J g :=
    continuous_subtype_val
  have hv : Continuous fun g : HA (Ainf F) σ J =>
      ((HA.mat (Ainf F) σ J g : GL (Fin n) (Ainf F ⊗[F] E)) :
        Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) := Units.continuous_val.comp hm
  refine continuous_pi fun b => ?_
  exact (hv.comp continuous_fst).matrix_mulVec ((continuous_apply b).comp continuous_snd)

end GlobalTheory.ArchUnitaryTop
