import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.NumFieldHosCountable
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.HfinExistsMat
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.FdomExistsAll

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta MeasureTheory NumberField

namespace Formalism.IndefR.Eqv

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable (D : D7)

theorem ga_facts (V : HSp D) :
    IsTopologicalGroup (GA D V) ∧ T2Space (GA D V) ∧ LocallyCompactSpace (GA D V) ∧
      SecondCountableTopology (GA D V) ∧ BorelSpace (GA D V) := by
  obtain ⟨h1, h2, h3⟩ := G5.af_facts D.host.F
  exact G5.ha_facts (AF D.host.F) D.sp.cm.deg2 D.sp.cm.sig V.gram

theorem ae_facts : IsTopologicalRing (AE D) ∧ T2Space (AE D) ∧ LocallyCompactSpace (AE D) ∧
    SecondCountableTopology (AE D) ∧ BorelSpace (AE D) := by
  obtain ⟨h1, h2, h3⟩ := G5.af_facts D.host.F
  exact G5.tens_facts (AF D.host.F) D.sp.cm.deg2

theorem gQDiscrete_holds : GQDiscrete D := fun V => G5.hfin_disc D.sp.cm.sig V.gram

theorem gQ_countable (V : HSp D) : Countable (GQ V) := G5.hfin_countable D.sp.cm.sig V.gram

theorem measurableMul_GA (V : HSp D) : MeasurableMul (GA D V) := by
  obtain ⟨h1, -, -, -, h5⟩ := ga_facts D V
  infer_instance

theorem measurableMul₂_GA (V : HSp D) : MeasurableMul₂ (GA D V) := by
  obtain ⟨h1, -, -, h4, h5⟩ := ga_facts D V
  infer_instance

theorem gfC_secondCountable (V : HSp D) : SecondCountableTopology (GfC V) := by
  obtain ⟨-, -, -, h4, -⟩ := ga_facts D V
  exact Topology.IsInducing.subtypeVal.secondCountableTopology

theorem fundDomExists_holds : FundDomExists D := fun V => by
  obtain ⟨h1, -, -, h4, h5⟩ := ga_facts D V
  have := gQDiscrete_holds D V
  exact G5.fdom_exists_all (GQ V)

end Formalism.IndefR.Eqv

end
