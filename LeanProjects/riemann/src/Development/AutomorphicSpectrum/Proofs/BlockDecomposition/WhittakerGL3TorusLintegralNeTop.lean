import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TauL

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection
open scoped NumberField.AdeleRing ValuativeRel ENNReal
open Ad3 Ad3.K Ad3.K.GPK GlobalTheory.CompanionTheory.GPKIntB

namespace GlobalTheory.CompanionTheory.GPKIntB.TauLoc

section
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

instance secondCountable_units' : SecondCountableTopology Fˣ :=
  (isOpenEmbedding_units_val (K := F)).isEmbedding.secondCountableTopology

variable [MeasurableSpace F] [BorelSpace F]

end

end GlobalTheory.CompanionTheory.GPKIntB.TauLoc
