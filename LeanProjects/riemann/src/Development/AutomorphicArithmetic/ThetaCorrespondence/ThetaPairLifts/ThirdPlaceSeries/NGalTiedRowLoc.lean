import Formalism.LocalToGlobal.GaloisLevelStructure.TiedRowLoc
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain
namespace Formalism.L2
structure RowLocTiedAlt (D : D7) (lp : LPTiedPlaceholder D) (F : RowFrame D) : Prop where
  sat : ∀ (i : D.nd.Loc) (σ : D.what₂.FT) v (w : PlE D.host), NG.OverPl w v → ∀ (Dv : InertDatum D.host.E D.R.r v w),
    (∃ α, NG.SatAtS (F.rep σ).S Dv α) → ∃ α, NG.SatAtS (F.rep σ).S Dv α ∧ D.naut.satW i σ w = Finset.univ.val.map α
end Formalism.L2
end
end
