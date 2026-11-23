import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.QuasiOfFam

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Unf.FB

variable {D : D7}

def IsFundU {ρ : ℕ} (v : VolU D ρ) (𝓤 : Set (UX D ρ)) : Prop := IsFundamentalDomain (UXQ D ρ) 𝓤 v.ν

theorem exists_isFundU {ρ : ℕ} (v : VolU D ρ) : ∃ 𝓤, IsFundU v 𝓤 ∧ v.ν 𝓤 = 1 := v.unit.2

end GlobalTheory.Unf.FB

end
