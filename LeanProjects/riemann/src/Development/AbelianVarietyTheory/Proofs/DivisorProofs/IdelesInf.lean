import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
open scoped TensorProduct NNReal Matrix
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section
namespace GlobalTheory.ThKCtFin

variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def idelesInf : Set (AE F E)ˣ := {a | At (evI F) ((a : AE F E) - 1)}

def idelesFin : Set (AE F E)ˣ := {u | At (fun x : AF F => x.2) ((u : AE F E) - 1)}

example : (1 : (AE F E)ˣ) ∈ idelesInf F E := fun _ _ => by simp
example : (1 : (AE F E)ˣ) ∈ idelesFin F E := fun _ _ => by simp

end GlobalTheory.ThKCtFin
