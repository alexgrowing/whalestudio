import Mathlib
import ReciprocityTheory.ClassFieldTheory.LocalClassField.ExistsIntEKMulVbar
import ReciprocityTheory.ClassFieldTheory.LocalClassField.Kummer
import ReciprocityTheory.ClassFieldTheory.LocalClassField.FinCoh
import ReciprocityTheory.ClassFieldTheory.LocalClassField.EqZeroOfResEqZeroOfCoprime

namespace ReciprocityTheory.DiscreteGroups.LocalClassField

open _root_.Neutral.B1 ReciprocityTheory.Coh Function

variable (p : ℕ) [Fact p.Prime] (K L : IntermediateField ℚ_[p] (PadicAlgCl p))

variable {p}

noncomputable def intLinOfAdd {A B : Type*} [AddCommGroup A] [AddCommGroup B] [Module ℤ A] [Module ℤ B] (f : A →+ B) :
    A →ₗ[ℤ] B where
  toFun := f
  map_add' := f.map_add
  map_smul' k x := by simpa using map_intCast_smul f ℤ ℤ k x

scoped instance discreteTopology_muT (F : IntermediateField ℚ_[p] (PadicAlgCl p)) (l : ℕ) [NeZero l] :
    DiscreteTopology (Kummer.muT p F l).V :=
  inferInstanceAs (DiscreteTopology (ZMod l))

end ReciprocityTheory.DiscreteGroups.LocalClassField
