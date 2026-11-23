import Mathlib
import Formalism.PeriodIntegrals.VolSemiDirect
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.ClosedStep
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.TensTopOf

noncomputable section

namespace PI.VolSemiDirect.W.Lc

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory
open scoped TensorProduct

theorem lcscHA_of (hT : TensTop) : LcscHA := by
  intro F E _ _ _ _ _ σ hCM M J hJ
  obtain ⟨htr, ht2, hlc, hsc⟩ := hT F E
  have : Module.Finite F E := finite_nf F E
  have : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  have hs : Continuous (sigR (AF F) σ) :=
    IsModuleTopology.continuous_of_linearMap (R := AF F) (sigL (AF F) σ)
  have hcl : IsClosed ((HR (AF F) σ J : Subgroup (GL (Fin M) (AF F ⊗[F] E))) :
      Set (GL (Fin M) (AF F ⊗[F] E))) := by
    have hc : Continuous fun g : GL (Fin M) (AF F ⊗[F] E) =>
        Formalism.UG.cT (sigR (AF F) σ) (g : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) * JR (AF F) J *
          (g : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) := by
      unfold Formalism.UG.cT
      have h0 : Continuous fun g : GL (Fin M) (AF F ⊗[F] E) =>
          (g : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) := Units.continuous_val
      exact (((h0.matrix_map hs).matrix_transpose).matrix_mul continuous_const).matrix_mul h0
    exact isClosed_eq hc continuous_const
  have hMlc : LocallyCompactSpace (Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) :=
    inferInstanceAs (LocallyCompactSpace (Fin M → Fin M → AF F ⊗[F] E))
  have hMsc : SecondCountableTopology (Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) :=
    inferInstanceAs (SecondCountableTopology (Fin M → Fin M → AF F ⊗[F] E))
  have hMt2 : T2Space (Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) :=
    inferInstanceAs (T2Space (Fin M → Fin M → AF F ⊗[F] E))
  have hMosc : SecondCountableTopology (Matrix (Fin M) (Fin M) (AF F ⊗[F] E))ᵐᵒᵖ :=
    (MulOpposite.opHomeomorph (M := Matrix (Fin M) (Fin M) (AF F ⊗[F] E))).symm.isEmbedding.secondCountableTopology
  have hGe := Units.isClosedEmbedding_embedProduct (α := Matrix (Fin M) (Fin M) (AF F ⊗[F] E))
  have hGlc : LocallyCompactSpace (GL (Fin M) (AF F ⊗[F] E)) := hGe.locallyCompactSpace
  have hGsc : SecondCountableTopology (GL (Fin M) (AF F ⊗[F] E)) :=
    hGe.isEmbedding.secondCountableTopology
  have hGt2 : T2Space (GL (Fin M) (AF F ⊗[F] E)) := hGe.isEmbedding.t2Space
  have r : LCSC (HR (AF F) σ J) :=
    ⟨hcl.isClosedEmbedding_subtypeVal.locallyCompactSpace,
      hcl.isClosedEmbedding_subtypeVal.isEmbedding.secondCountableTopology, inferInstance,
      inferInstance⟩
  exact r

end PI.VolSemiDirect.W.Lc
