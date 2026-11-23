import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsobaricDiscreteSelfDualStrongMultiplicityOne
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RankOneUnitary
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TraceNondegenerateOfIsSSRep
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.NRows

theorem isHeckeGaloisQ_of_isHeckeGalois : ∀ (D : D7) (i : D.nd.Loc) (x : D.nd.X i)
    (r : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin D.R.nV) (D.nd.O i)),
    IsHeckeGalois D.nd i x r → SumRepresentations.At.IsHeckeGaloisQ D.nd D.naut i x (mapRep (iotaOQ D.nd D.naut i) r) := by
  intro D i x r hr
  refine ⟨SumRepresentations.contQ_of_continuous D.nd D.naut i r hr.1, ?_, ?_⟩
  · have : CharZero (Kf D.nd i) := RingHom.charZero (D.naut.iotaQ i)
    have h := GlobalTheory.TraceSemisimple.isSSRep_mapRep _ _ _ (D.naut.iotaQ i) _ _ hr.2.1
    have e : mapRep (iotaOQ D.nd D.naut i) r =
        mapRep (D.naut.iotaQ i) (mapRep (algebraMap (D.nd.O i) (Kf D.nd i)) r) := by
      ext g a b
      rfl
    rw [e]
    exact h
  · intro w hw B σ hB hσ
    have e3 : ((mapRep (iotaOQ D.nd D.naut i) r σ : GL _ _) : Matrix (Fin D.R.nV) (Fin D.R.nV) (Qbar (D.nd.l i))) =
        ((r σ : GL _ _) : Matrix (Fin D.R.nV) (Fin D.R.nV) (D.nd.O i)).map (iotaOQ D.nd D.naut i) := rfl
    rw [e3, Matrix.charpoly_map, hr.2.2 w hw B σ hB hσ]

end GlobalTheory.NRows
