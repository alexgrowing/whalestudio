import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIsAdelicGlueVectorOfGlueBaseData
import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemHatIffOfSelfDual
open Formalism.BasicNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Matrix
open Formalism.L2.DIV (Pl)
open Formalism.IndefR.Lev (EAf)
open Formalism.IndefR.Datum (IsSelfDualC)
open GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents GlobalTheory.AdIsom
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isAdelicGlueVector_of_glueBaseData : ∀ (D : D7) (u : D.what₂.Word) (π : 𝓞 D.host.E), IsPi u π → ∀ (X : HSp D) (L₀ : Lat X) (f₀ : Pl D.host.E → Fin X.rank → EAf D), IsBasePair X u π L₀ f₀ → ∃ f, IsGlueVec X u L₀ f ∧ ∀ w : Pl D.host.E, π ∈ w.asIdeal → idem w • f = f₀ w := by
  first | exact @GlobalTheory.AdIsom.BaseVec.exists_isGlueVec | exact GlobalTheory.AdIsom.BaseVec.exists_isGlueVec | (intros; apply GlobalTheory.AdIsom.BaseVec.exists_isGlueVec <;> assumption)
