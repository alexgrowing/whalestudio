import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TendstoPlaceComponentsFiniteAdelicUnitary
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnitaryOnTheta
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnrOffOne
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR GlobalTheory.WeilParts
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tendsto_placeComponents_finiteAdelicUnitary : ∀ (D : D7) (V : HSp D) (g : GA D V), g ∈ GfC V → ∀ (ε : HeightOneSpectrum (𝓞 D.host.F) → AF D.host.F), (∀ v, IsPlaceIdem D v (ε v)) → ∀ gs : Finset (HeightOneSpectrum (𝓞 D.host.F)) → GA D V, (∀ A, Formalism.L2.Theta.mt V (gs A) = algebraMap (AF D.host.F) (AE D) (∑ v ∈ A, ε v) • Formalism.L2.Theta.mt V g + (1 - algebraMap (AF D.host.F) (AE D) (∑ v ∈ A, ε v)) • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D))) → Filter.Tendsto gs Filter.atTop (nhds g) := by
  first | exact @GlobalTheory.PlaceLimit.tendsto_components | exact GlobalTheory.PlaceLimit.tendsto_components | (intros; apply GlobalTheory.PlaceLimit.tendsto_components <;> assumption)
