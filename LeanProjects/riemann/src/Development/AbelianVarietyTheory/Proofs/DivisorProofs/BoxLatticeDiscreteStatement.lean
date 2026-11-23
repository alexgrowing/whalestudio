import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoxLatticeDiscrete
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenScaledInt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanTracePairingBilinearNondegenerate
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAdelicCharacterNontrivialAtPlaces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PsiFinRat

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open scoped Classical
open GlobalTheory.BoxLattice GlobalTheory.EvAdm

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.box_lattice_discrete : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (a : F),
    DiscreteTopology (boxLat F κ a) := by
  first | exact @GlobalTheory.BoxLattice.boxLat_discrete | exact GlobalTheory.BoxLattice.boxLat_discrete | (intros; apply GlobalTheory.BoxLattice.boxLat_discrete <;> assumption)
