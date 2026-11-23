import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdeleStabilizerIsOpen
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DecayNonneg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsInfEqOne

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.idele_stabilizer_isOpen : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E],
    IsOpen ((GlobalTheory.IdeleTate.stab F E : Subgroup (AE F E)ˣ) : Set (AE F E)ˣ) := by
  first | exact @GlobalTheory.IdeleTate.isOpen_stab | exact GlobalTheory.IdeleTate.isOpen_stab | (intros; apply GlobalTheory.IdeleTate.isOpen_stab <;> assumption)
